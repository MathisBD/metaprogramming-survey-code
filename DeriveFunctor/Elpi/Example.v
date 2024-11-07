From DeriveFunctor.Elpi Require Import Command.

Elpi DeriveFunctor list.
Elpi DeriveFunctor option.

Inductive tree A :=
  | Leaf : A -> tree A
  | Node : bool -> list (option (tree A)) -> tree A.
Elpi DeriveFunctor tree.

Inductive tree2 A :=
  | T : list (tree (option A)) -> tree2 A.
Elpi DeriveFunctor tree2.
