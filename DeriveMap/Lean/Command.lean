import Lean
import DeriveMap.Lean.NameDb
open Lean Meta Elab

/- --------------------------------------------------------------------------------------/
/- Utilities. -/
/- --------------------------------------------------------------------------------------/

/-- `freshConstant c` returns the (universe polymorphic) constant `c` applied
    to the right number of fresh universe levels.  -/
def freshConstant (cinfo : ConstantInfo) : MetaM Expr := do
  let lvls ← cinfo.levelParams.mapM fun _ => mkFreshLevelMVar
  return .const cinfo.name lvls

/-- `subterm x t` is `true` if `x` occurs in `t` (modulo alpha equivalence). -/
partial def subterm (x t : Expr) : Bool :=
  if Expr.eqv x t
  then true
  else Id.run $ Expr.foldlM (fun res subt => return res || subterm x subt) false t

/- --------------------------------------------------------------------------------------/
/- Lifting mapping functions. -/
/- --------------------------------------------------------------------------------------/
namespace Lift

/-- A lifting problem consists in lifting a function `f : A → B` to a function `T → U`.
    It is expected that `U` is equal to `T` with `A` replaced by `B`. -/
structure Problem where
  A : Expr
  B : Expr
  f : Expr
  T : Expr
  U : Expr
deriving instance Inhabited, Repr for Problem

/-- A lifting rule tries to solve lifting problems : it either returns a solution `some f'`
    with `f' : T → U` or fails with `none`.

    Lifting rules execute in `MetaM` because they need to perform unification. -/
def Rule := Problem → MetaM (Option Expr)
deriving instance Inhabited for Rule

/-- A basic lifting rule which solves the problem when `T` is equal to `A`,
    in which case `f' = f`. -/
def rule_apply : Rule := fun lp => do
  IO.println s!"RULE apply ON { ← ppExpr lp.T}"
  if ← isDefEq lp.A lp.T
  then do
    IO.println s!">>Success"
    return some lp.f
  else do
    IO.println s!">>Fail"
    return none

/-- A basic lifting rule which solves the problem when `T` does not contain `A`,
    in which case `f' = fun x : T => x`. -/
def rule_id : Rule := fun lp => do
  IO.println s!"RULE id ON { ← ppExpr lp.T }"
  if subterm lp.A lp.T
  then do
    IO.println s!">>Fail"
    return none
  else do
    IO.println s!">>Success"
    return some $ Expr.lam `x lp.T (.bvar 0) BinderInfo.default

/-- `mzero` is a lifting rule which always fails. -/
def mzero : Rule := fun _ => return none

/-- `msum r1 r2` tries to apply rule `r1` and if it fails applies rule `r2`. -/
def msum (r1 r2 : Rule) : Rule := fun lp => do
  match ← r1 lp with
  | none => r2 lp
  | some f' => return some f'

/-- `sequence rs` tries to apply the rules in `rs` in order (from left to right)
    until one succeeds. -/
def sequence (rs : List Rule) : Rule :=
  match rs with
  | [] => mzero
  | r :: rs => List.foldl msum r rs

/-- `detruct_map f` checks that `f` is a mapping function i.e. has type

    `f.{u1,u2} : forall (A :Type u1) (B : Type u2), (A -> B) -> I.{u1} A -> I.{u2} B`

    where `I` is the name of a constant. It returns `some I` if it succeeds or `none` if it fails. -/
def destruct_map (f : Expr) : MetaM (Option Name) := do
  -- Make the pattern with which we will unify.
  let u1 ← mkFreshLevelMVar
  let u2 ← mkFreshLevelMVar
  let I1 ← mkFreshExprMVar $ some $ ← mkArrow (.sort u1) (.sort u1)
  let I2 ← mkFreshExprMVar $ some $ ← mkArrow (.sort u2) (.sort u2)
  let pat ←
    withLocalDecl `A BinderInfo.default (.sort u1) fun A => do
    withLocalDecl `B BinderInfo.default (.sort u2) fun B => do
      let arrs ← mkArrowN #[← mkArrow A B, .app I1 A] (.app I2 B)
      mkForallFVars #[A, B] arrs
  -- Unify the type of f with the pattern.
  let ty ← inferType f
  if ← isDefEq ty pat
  then do
    let I1 ← instantiateMVars I1
    let I2 ← instantiateMVars I2
    -- Check that I1 = I.{u1} and I2 = I.{u2}.
    match I1, I2 with
    | .const I1_name _, .const I2_name _ =>
      return if I1_name = I2_name then some I1_name else none
    | _, _ => return none
  else return none

def custom_rule (rec_rule : Rule) (map_name : Name) : Rule := fun lp => do
  IO.println s!"RULE {map_name} ON { ← ppExpr lp.T }"
  -- Extract the type former T.
  let map ← freshConstant =<< getConstInfo map_name
  let tf := Option.get! (← destruct_map map)
  -- Create unification variables alpha and beta.
  let uAlpha ← mkFreshLevelMVar
  let uBeta ← mkFreshLevelMVar
  let alpha ← mkFreshExprMVar $ some $ .sort uAlpha
  let beta ← mkFreshExprMVar $ some $ .sort uBeta
  -- Unify T =?= tf alpha and U =?= tf beta.
  let b1 ← isDefEq lp.T $ .app (← freshConstant =<< getConstInfo tf) alpha
  let b2 ← isDefEq lp.U $ .app (← freshConstant =<< getConstInfo tf) beta
  if b1 && b2 then do
    let alpha ← instantiateMVars alpha
    let beta ← instantiateMVars beta
    IO.println s!">>Recursing on { ← ppExpr alpha} → { ← ppExpr beta }"
    -- Recurse to lift f : A -> B to f' : alpha -> beta
    let f' ← rec_rule { lp with T := alpha, U := beta }
    match f' with
    | none => do
      IO.println s!">>Fail"
      return none
    | some f' => do
      IO.println s!">>Success"
      return mkAppN map #[alpha, beta, f']
  else return none

partial def fix (f : Rule → Rule) : Rule :=
  fun lp => f (fix f) lp

end Lift

/- --------------------------------------------------------------------------------------/
/- Actual #derive_map and #add_map implementation. -/
/- --------------------------------------------------------------------------------------/

def buildBranch (u0 u1 : Level) (A B f : Expr) (ctr : ConstructorVal) : MetaM Expr := do
  -- Get the type of the constructor.
  let ctr_ty ← instantiateTypeLevelParams (ConstantInfo.ctorInfo ctr) [u0]
  -- Get the arguments of the constructor applied to A.
  forallTelescope (← instantiateForall ctr_ty #[A]) fun args _ => do
    -- Map over each argument of the constructor.
    let mapped_args ← args.mapM fun arg => do
      -- Construct the lifting problem.
      let T ← LocalDecl.type <$> Meta.getFVarLocalDecl arg
      -- Take case to also replace `u0` by `u1` when computing `U`.
      let U := Expr.replaceLevel (fun u => if u == u0 then some u1 else none) $ Expr.replaceFVar T A B
      let lp := { A, B, f, T, U : Lift.Problem }
      -- Construct a lifting rule.
      let map_funcs ← NameDb.get
      let rule :=
        Lift.fix fun rec_rule =>
          Lift.sequence $ Lift.rule_apply :: Lift.rule_id :: List.map (Lift.custom_rule rec_rule) map_funcs
      -- Solve the lifting problem.
      match ← rule lp with
      | none => throwError s!"Could not lift function of type {← ppExpr A} → {← ppExpr B} on argument of type {← ppExpr T}"
      | some f' => return Expr.app f' arg
    -- Apply the constructor to the new arguments.
    let fresh_ctr ← freshConstant $ .ctorInfo ctr
    let body := mkAppN fresh_ctr $ Array.append #[B] mapped_args
    -- Abstract with respect to the arguments.
    instantiateMVars =<< mkLambdaFVars args body

/-- Build the mapping function : we return the function as an `Expr`,
    and since the mapping function is universe polymorphic we also return
    the names of its universe parameters. -/
def buildMap (ind : InductiveVal) : MetaM (List Name × Expr) := do
  -- Helper to apply the inductive to a parameter.
  let apply_ind param : MetaM Expr := do
    return Expr.app (← freshConstant $ .inductInfo ind) param
  -- Create some universe level parameters.
  let u0 := `u0
  let u1 := `u1
  -- Declare the inputs of the function (add them to the local context).
  withLocalDecl `A BinderInfo.implicit (.sort $ .succ $ .param u0)    fun A => do
  withLocalDecl `B BinderInfo.implicit (.sort $ .succ $ .param u1)    fun B => do
  withLocalDecl `f BinderInfo.default  (← mkArrow A B)                fun f => do
  withLocalDecl `x BinderInfo.default  (← apply_ind A) fun x => do
    -- Construct the match return type (as a function of the scrutinee x).
    let ret_type := Expr.lam `_ (← apply_ind A) (← apply_ind B) BinderInfo.default
    -- Construct the match branches. Each branch is a lambda abstraction which
    -- takes as input the *non-parameter* arguments of the constructor.
    let branches ← ind.ctors.toArray.mapM fun ctr => do
      let info ← getConstInfoCtor ctr
      buildBranch (.param u0) (.param u1) A B f info
    -- Construct the match expression.
    let cases_func ← freshConstant (← getConstInfo $ .str ind.name "casesOn")
    let body := mkAppN cases_func $ Array.append #[A, ret_type, x] branches
    -- Bind the input parameters.
    let res ← mkLambdaFVars #[A, B, f, x] body
    -- Return the level parameters and the resulting function.
    return ⟨[u0, u1], res⟩

/-- `DeriveMap` command entry point. -/
def deriveMap (ind_name : Name) : MetaM Unit := do
  -- Resolve the inductive.
  let ind ← getConstInfoInduct ind_name
  -- Build the function.
  let ⟨lvls, body⟩ ← buildMap ind
  IO.println s!"Levels : { lvls }"
  IO.println s!"Body :\n{ ← ppExpr body }"
  -- Typecheck the function to instantiate any remaining metavariables & level metavariables.
  check body
  let body ← instantiateMVars body
  -- Choose a name for the mapping function.
  let map_name := Name.str ind_name "map"
  -- Add the function to the global environment.
  let defVal ←
    mkDefinitionValInferrringUnsafe
      map_name lvls (← inferType body) body (ReducibilityHints.regular 0)
  addDecl $ Declaration.defnDecl defVal
  IO.println s!"Declared mapping function for `{ind_name} under the name `{map_name}"

/-- Derive a mapping function for an inductive.
    Only works for inductives which have exactly one *uniform* parameter. -/
elab "#derive_map" ind_name:name : command =>
  Command.liftTermElabM $ deriveMap ind_name.getName

/-- Add a mapping function to the database. -/
elab "#add_map" func_name:name : command =>
  Command.liftTermElabM do
    -- Check the function is a mapping function.
    let func ← getConstInfo func_name.getName
    match ← Lift.destruct_map $ ← freshConstant func with
    -- This is not a mapping function : fail.
    | none => throwError s!"Provided constant is not a mapping function."
    -- Add the function to the database.
    | some _ => NameDb.extend func_name.getName

/- --------------------------------------------------------------------------------------/
/- Examples. -/
/- --------------------------------------------------------------------------------------/

inductive Double (A : Type u) : Type u :=
  | double : A -> A -> Double A

#derive_map `Double
#add_map `Double.map

#print Double.map

inductive Mylist (A : Type u) : Type u :=
  | nil : Bool → Mylist A
  | duh : A → A → Mylist A
  | cons : A → List A → Bool → Double (List A) → Mylist A

#add_map `List.map
#derive_map `Mylist
