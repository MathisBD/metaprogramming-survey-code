Declare ML Module "coq-metaprogramming.derivemap.plugin".

Require List.

AddMap @List.map.

Inductive tree A :=
  | Leaf : A -> tree A
  | Node : bool -> tree (list A) -> list (list (tree A)) -> tree A.

DeriveMap tree.

(*Check tree_map.*)