import Lean
open Lean Meta Elab

-- A stock inductive type.
-- Originally I wanted to define lists but it evolved into something else...
inductive Mylist (A : Type u) : Type u :=
  | nil : Bool -> Mylist A
  | cons : A → A → Mylist A

-- A standard *mapping* function.
-- Below I recreate this function by building `Expr`s directly.
def Mylist.map (f : α → β) (x : Mylist α) : Mylist β :=
  match x with
  | .nil b => .nil b
  | .cons x1 x2 => .cons (f x1) (f x2)

-- Under the hood `match` expressions are implemented in Lean using a special function :
-- here it is `Mylist.casesOn`.
#check Mylist.casesOn
-- `.casesOn` takes as input :
-- 1. The type of the inductive parameter : in our case `A`
-- 2. The return type of the match, which can depend on `x` : in our case `fun _ => Mylist B`
-- 3. The scrutinee of the match : in our case `x`
-- 4. A function for each branch of the match, which abstracts over the indices (not the parameters)
--    of the inductive : in our case
--    4.1 the nil branch : `fun b => .nil b`
--    4.2 the cons branch : `fun x1 x2 => .cons (f x1) (f x2)`

---------------------------------------------------------------------------------------
-- We now want to define `Mylist.map` using `Expr`s.
-- To do so we will work in the `MetaM` monad, which allows us to use the global environment
-- and use metavariables (for unification/typechecking).

/-- `freshConstant c` returns the (universe polymorphic) constant `c` applied
    to the right number of fresh universe levels.  -/
def freshConstant (c : Name) : MetaM Expr := do
  let cinfo ← getConstInfo c
  let lvls ← cinfo.levelParams.mapM fun _ => mkFreshLevelMVar
  return .const c lvls

-- Build the mapping function : we return the function as an `Expr`,
-- and since the mapping function is universe polymorphic we also return
-- the names of its universe parameters.
def build_map : MetaM (List Name × Expr) := do
  -- Create some universe level parameters.
  let u0 := `u0
  let u1 := `u1
  -- Declare the inputs of the function (add them to the local context).
  withLocalDecl `A BinderInfo.implicit (.sort $ .succ $ .param u0) fun A => do
  withLocalDecl `B BinderInfo.implicit (.sort $ .succ $ .param u1) fun B => do
  withLocalDecl `f BinderInfo.default  (← mkArrow A B)              fun f => do
  withLocalDecl `x BinderInfo.default  (← mkAppM ``Mylist #[A])     fun x => do
    -- Construct the match return type (as a function of the scrutinee x).
    let ret_type := Expr.lam `_ (← mkAppM ``Mylist #[A]) (← mkAppM ``Mylist #[B]) BinderInfo.default
    -- Construct the match branches. Each branch is a lambda abstraction which
    -- takes as input the *non-parameter* arguments of the constructor.
    let branch_nil ←
      withLocalDecl `arg1 BinderInfo.default (.const ``Bool []) fun arg1 => do
        let body := mkAppN (← freshConstant ``Mylist.nil) #[B, arg1]
        mkLambdaFVars #[arg1] body
    let branch_cons ←
      withLocalDecl `arg1 BinderInfo.default A fun arg1 => do
      withLocalDecl `arg2 BinderInfo.default A fun arg2 => do
        let body := mkAppN (← freshConstant ``Mylist.cons) #[B, .app f arg1, .app f arg2]
        mkLambdaFVars #[arg1, arg2] body
    -- Construct the match expression.
    let body := mkAppN (← freshConstant ``Mylist.casesOn) #[A, ret_type, x, branch_nil, branch_cons]
    -- Bind the input parameters.
    let res ← mkLambdaFVars #[A, B, f, x] body
    -- Return the level parameters and the resulting function.
    return ⟨[u0, u1], res⟩

-- Code to declare the function.
def declare_map : MetaM Unit := do
  -- Build the function.
  let ⟨lvls, body⟩ ← build_map
  -- Typecheck the function to instantiate any remaining metavariables & level metavariables.
  check body
  let body ← instantiateMVars body
  -- Add the function to the global environment.
  let defVal ← mkDefinitionValInferrringUnsafe
    `Mylist.map2
    lvls
    (← inferType body)
    body
    (ReducibilityHints.regular 0)
  addDecl $ Declaration.defnDecl defVal

-- Actually declare the function.
#eval declare_map

-- Recall the original version.
#print Mylist.map

-- Our new version. It doesn't have the nice pretty-printing for the `match` expression,
-- I don't know how to get that yet.
#print Mylist.map2

-- The two versions are indeed the same.
example : @Mylist.map = @Mylist.map2 := by rfl
