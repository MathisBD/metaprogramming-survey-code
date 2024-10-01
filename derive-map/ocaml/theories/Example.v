Declare ML Module "coq-metaprogramming.derivemap.plugin".

Require List.

AddMap List.map.

Inductive tree A :=
  | Leaf : A -> tree A
  | Node : bool -> list A -> tree A.


DeriveMap tree.

(*Check tree_map.*)