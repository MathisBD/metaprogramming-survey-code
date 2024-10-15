Declare ML Module "coq-metaprogramming.derivemap.plugin".

Require List.

(*AddMap List.map.

Inductive tree A :=
  | Leaf : A -> tree A
  | Node : bool -> list (tree A) -> tree A.

DeriveMap tree.
*)