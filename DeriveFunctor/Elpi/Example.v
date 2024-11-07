From DeriveFunctor.Elpi Require Import Command.

Inductive double A := 
  | Double : A -> A -> double A.

Inductive tree A := 
  | Leaf : A -> nat -> tree A
  | Node : list (tree A) -> double A -> tree A -> tree A.

Inductive ind (A : Type) : Type :=
  | Con : tree (ind A) -> ind A.

(*Elpi DeriveMap double.
Elpi AddMap (@double_map).
Elpi DeriveMap list.
Elpi AddMap (@list_map).
Elpi DeriveMap tree.
Elpi AddMap (@tree_map).
Elpi DeriveMap ind.*)

(*Eval cbv in @ind_map.*)