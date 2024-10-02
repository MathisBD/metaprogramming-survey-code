import Lean
open Lean Meta Elab

set_option pp.universes true
set_option pp.explicit true

inductive Mylist (A : Type u) : Type u :=
  | nil : Bool -> Mylist A
  | cons : A → A → Mylist A

--def Mylist.map (f : α → β) (x : Mylist α) : Mylist β :=
--  match x with
--  | Mylist.nil b => Mylist.nil b
--  | Mylist.cons x1 x2 => Mylist.cons (f x1) (f x2)
--
--#check Mylist.map

def build_map : MetaM (List Name × Expr) := do
  -- Create some level parameters.
  let u0 := `u0
  let u1 := `u1
  withLocalDecl `A BinderInfo.implicit (.sort $ .succ $ .param u0) fun A => do
  withLocalDecl `B BinderInfo.implicit (.sort $ .succ $ .param u1) fun B => do
  withLocalDecl `f BinderInfo.default (← mkArrow A B) fun f => do
  withLocalDecl `x BinderInfo.default (← mkAppM ``Mylist #[A]) fun x => do
    let res ← mkLambdaFVars #[A, B, f, x] x
    return ⟨[u0, u1], res⟩

def register_map : MetaM Unit := do
  let ⟨lvls, body⟩ ← build_map
  let ty ← inferType body
  IO.println s!"type of map : { repr ty }"
  let defVal ← mkDefinitionValInferrringUnsafe
    `Mylist.map
    lvls
    ty
    body
    (ReducibilityHints.regular 0)
  addDecl (Declaration.defnDecl defVal)

#eval register_map

#print Mylist.map

----------------------------------------

elab "#show_expr" t:term : command =>
  Command.liftTermElabM do
    let e ← Term.elabTerm t Option.none
    let e ← instantiateMVars e
    IO.println s!"{← hasAssignedMVar e}"
    IO.println $ repr $ e

#show_expr (match 0 with | 0 => 0 | n + 1 => n)
