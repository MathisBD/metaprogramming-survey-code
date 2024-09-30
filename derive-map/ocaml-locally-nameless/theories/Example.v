Declare ML Module "coq-metaprogramming.derivemap.ocamllocallynameless.plugin".

Require List.

AddMap @List.map.

Inductive tree A :=
  | Leaf : A -> tree A
  | Node : bool -> list (list (tree A)) -> tree A.

DeriveMap tree.

(*Check tree_map.*)