Require Import DeriveFunctor.Functor.Functor.
Declare ML Module "coq-metaprogramming.derivefunctor.plugin".
Require List.

Derive Functor for option.
Derive Functor for list.

Inductive tree A :=
  | Leaf : A -> tree A
  | Node : bool -> list (option (tree A)) -> tree A.
Derive Functor for tree.

Inductive tree2 A :=
  | T : list (tree (option A)) -> tree2 A.
Derive Functor for tree2.
