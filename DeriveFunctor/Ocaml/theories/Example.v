Require Import DeriveFunctor.Functor.Functor.
Declare ML Module "coq-metaprogramming.derivefunctor.plugin".
Require List.

Derive Functor for option.
Derive Functor for list.

(*Eval cbv zeta beta iota in fix fmap_rec (a b : Type) (f : a -> b) (x : list a) {struct x} :
list b :=
let rec_inst := {| fmap := fmap_rec |} in
match x with
| nil => nil
| (x0 :: x1)%list => (f x0 :: fmap f x1)%list
end.*)

(*Instance : Functor list :=
{ fmap := fix fmap_rec (a b : Type) (f : a -> b) (x : list a) {struct x} :
list b :=
match x with
| @nil _ => @nil b
| (x0 :: x1)%list =>
  (f x0 :: @fmap list {| fmap := fmap_rec |} a b f x1)%list
end}.*)

Inductive tree A :=
  | Leaf : A -> tree A
  | Node : bool -> list (option (tree A)) -> tree A.
Derive Functor for tree.

Inductive tree2 A :=
  | T : list (tree (option A)) -> tree2 A.
Derive Functor for tree2.
