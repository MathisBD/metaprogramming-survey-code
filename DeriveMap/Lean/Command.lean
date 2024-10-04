import Lean
import DeriveMap.Lean.NameDb
open Lean Meta Elab

--inductive Tree (A : Type u) where
--  | node : A → List (Tree A) → Tree A
--
--unsafe def Tree.map {α β} (f : α → β) : Tree α → Tree β
--  | node v ts => node (f v) (List.map (fun t => Tree.map f t) ts)
--
--set_option pp.all true in
--#print Tree.map
--
--#print List.casesOn
--
--#print List.brecOn

inductive Mylist (A : Type u) : Type u :=
  | nil : Bool -> Mylist A
  | cons : A → A → Mylist A

/-- `freshConstant c` returns the (universe polymorphic) constant `c` applied
    to the right number of fresh universe levels.  -/
def freshConstant (c : Name) : MetaM Expr := do
  let cinfo ← getConstInfo c
  let lvls ← cinfo.levelParams.mapM fun _ => mkFreshLevelMVar
  return .const c lvls

/-- `subterm x t` is `true` if `x` occurs in `t` (modulo alpha equivalence). -/
partial def subterm (x t : Expr) : Bool :=
  if Expr.eqv x t
  then true
  else Id.run $ Expr.foldlM (fun res subt => return res || subterm x subt) false t

namespace Lift

/-- A lifting problem consists in lifting a function `f : A → B` to a function `T → U`.
    It is expected that `U` is equal to `T` with `A` replaced by `B`. -/
structure Problem where
  A : Expr
  B : Expr
  f : Expr
  T : Expr
  U : Expr
deriving instance Repr for Problem

/-- A lifting rule tries to solve lifting problems : it either returns a solution `some f'`
    with `f' : T → U` or fails with `none`.

    Lifting rules execute in `MetaM` because they need to perform unification. -/
def Rule := Problem → MetaM (Option Expr)

/-- A basic lifting rule which solves the problem when `T` is equal to `A`,
    in which case `f' = f`. -/
def rule_apply : Rule := fun lp => do
  if ← isDefEq lp.A lp.T
  then return some lp.f
  else return none

/-- A basic lifting rule which solves the problem when `T` does not contain `A`,
    in which case `f' = fun x : T => x`. -/
def rule_id : Rule := fun lp => do
  if subterm lp.A lp.T
  then return none
  else return some $ Expr.lam `x lp.T (.bvar 0) BinderInfo.default

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

end Lift

def buildBranch (A B f : Expr) (ctr : ConstructorVal) : MetaM Expr := do
  -- Get the type of the constructor at `A`.l
  let ctr_ty ← instantiateForall ctr.type #[A]
  -- Get the arguments of the constructor.
  forallTelescope ctr_ty fun args _ => do
    -- Map over each argument of the constructor.
    let mapped_args ← args.mapM fun arg => do
      -- Construct the lifting problem.
      let arg_ty := LocalDecl.type $ ← Meta.getFVarLocalDecl arg
      let lp := { A, B, f, T := arg_ty, U := Expr.replaceFVar arg_ty A B : Lift.Problem }
      -- Construct a lifting rule.
      let rule := Lift.sequence [Lift.rule_apply, Lift.rule_id]
      -- Solve the lifting problem.
      match ← rule lp with
      | none => throwError s!"Could not lift function of type {← ppExpr A} → {← ppExpr B} on argument of type {← ppExpr arg_ty}"
      | some f' => return Expr.app f' arg
    -- Apply the constructor to the new arguments.
    let body := mkAppN (← freshConstant ctr.name) $ Array.append #[B] mapped_args
    -- Abstract with respect to the arguments.
    mkLambdaFVars args body

/-- Build the mapping function : we return the function as an `Expr`,
    and since the mapping function is universe polymorphic we also return
    the names of its universe parameters. -/
def buildMap (ind : InductiveVal) : MetaM (List Name × Expr) := do
  -- Create some universe level parameters.
  let u0 := `u0
  let u1 := `u1
  -- Declare the inputs of the function (add them to the local context).
  withLocalDecl `A BinderInfo.implicit (.sort $ .succ $ .param u0)    fun A => do
  withLocalDecl `B BinderInfo.implicit (.sort $ .succ $ .param u1)    fun B => do
  withLocalDecl `f BinderInfo.default  (← mkArrow A B)                fun f => do
  withLocalDecl `x BinderInfo.default  (.app (← freshConstant ind.name) A) fun x => do
    -- Construct the match return type (as a function of the scrutinee x).
    let ret_type := Expr.lam `_ (.app (← freshConstant ind.name) A) (.app (← freshConstant ind.name) B) BinderInfo.default
    -- Construct the match branches. Each branch is a lambda abstraction which
    -- takes as input the *non-parameter* arguments of the constructor.
    let branches ← ind.ctors.toArray.mapM fun ctr => do
      let info ← getConstInfoCtor ctr
      buildBranch A B f info
    -- Construct the match expression.
    let body := mkAppN (← freshConstant ``Mylist.casesOn) $ Array.append #[A, ret_type, x] branches
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
  -- Typecheck the function to instantiate any remaining metavariables & level metavariables.
  check body
  let body ← instantiateMVars body
  -- Choose a name for the mapping function.
  -- TODO : ensure freshness (while maintaining a usable name).
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

-- Actually declare the function.
#derive_map `Mylist

#print Mylist.map

def foo : TermElabM Expr := do
  let stx ← `(term|
    let rec myListMap {α β} (f : α → β) (xs : List α) : List β :=
      match xs with
      | [] => []
      | x :: xs => f x :: myListMap f xs
    myListMap)
  instantiateMVars =<< Term.elabTerm stx none

#eval do
  let e ← foo
  IO.println s!"{ ← ppExpr e }"
