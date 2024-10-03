import Lean
open Lean Meta Elab

inductive Mylist (A : Type u) : Type u :=
  | nil : Bool -> Mylist A
  | cons : A → A → Mylist A

/-- `freshConstant c` returns the (universe polymorphic) constant `c` applied
    to the right number of fresh universe levels.  -/
def freshConstant (c : Name) : MetaM Expr := do
  let cinfo ← getConstInfo c
  let lvls ← cinfo.levelParams.mapM fun _ => mkFreshLevelMVar
  return .const c lvls

def buildBranch (A B f : Expr) (ctr : ConstructorVal) : MetaM Expr := do
  -- Get the type of the constructor at `A`.
  let ctr_ty ← instantiateForall ctr.type #[A]
  -- Get the arguments of the constructor.
  forallTelescope ctr_ty fun args _ => do
    -- Map over each argument of the constructor.
    let mapped_args ← args.mapM fun arg => do
      let arg_ty := LocalDecl.type $ ← Meta.getFVarLocalDecl arg
      let apply_f ← withNewMCtxDepth $ isDefEq arg_ty A
      if apply_f then return .app f arg else return arg
    -- Apply the constructor to the new arguments.
    let body := mkAppN (← freshConstant ctr.name) $ Array.append #[B] mapped_args
    -- Abstract with respect to the arguments.
    mkLambdaFVars args body

-- Build the mapping function : we return the function as an `Expr`,
-- and since the mapping function is universe polymorphic we also return
-- the names of its universe parameters.
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

-- Code to declare the function.
def deriveMap (ind_name : Name) : MetaM Unit := do
  -- Resolve the inductive.
  let ind ← getConstInfoInduct ind_name
  -- Build the function.
  let ⟨lvls, body⟩ ← buildMap ind
  -- Typecheck the function to instantiate any remaining metavariables & level metavariables.
  check body
  let body ← instantiateMVars body
  -- Choose a name for the mapping function, ensuring freshness.
  let map_name := Name.str ind_name "map"
  -- Add the function to the global environment.
  let defVal ← mkDefinitionValInferrringUnsafe
    map_name
    lvls
    (← inferType body)
    body
    (ReducibilityHints.regular 0)
  addDecl $ Declaration.defnDecl defVal
  IO.println s!"Declared mapping function for `{ind_name} under the name `{map_name}"

/-- Derive a mapping function for an inductive.
    Only works for inductives which have exactly one *uniform* parameter. -/
elab "#derive_map" ind_name:name : command =>
  Command.liftTermElabM $ deriveMap ind_name.getName

-- Actually declare the function.
#derive_map `Mylist

#print Mylist.map
