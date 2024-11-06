From Ltac2 Require Import Ltac2.
From DeriveFunctor.Functor Require Import Functor.
From DeriveFunctor.Ltac2 Require Import Command.
From Coq Require List.

Instance option_functor : Functor option. derive_functor (). Defined.
Instance list_functor : Functor list. derive_functor (). Defined.

Inductive tree A :=
  | Leaf : A -> tree A
  | Node : bool -> list (option (tree A)) -> tree A.
Instance tree_functor : Functor tree. derive_functor (). Defined.

Inductive tree2 A :=
  | T : list (tree (option A)) -> tree2 A.
Instance tree2_functor : Functor tree2. derive_functor (). Defined.

Print tree_functor.


 
