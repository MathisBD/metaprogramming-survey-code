Declare ML Module "derive-functor.plugin".
Require List.

(*************************************************************************************)
(** *** Functor typeclass.  *)
(*************************************************************************************)

(** The [Functor] typeclass. *)
Class Functor (F : Type -> Type) : Type :=
{ fmap {A B} : (A -> B) -> F A -> F B }.

(** The identity function is a functor. *)
Definition Id (A : Type) := A.
#[export] Instance functor_id : Functor Id := { fmap _ _ f a := f a }.

(** Composition of functors is still a functor. *)
#[export] Instance functor_comp F G `(Functor F) `(Functor G) : Functor (fun T => G (F T)) :=
{ fmap _ _ f := @fmap G _ _ _ (@fmap F _ _ _ f) }.

(*************************************************************************************)
(** *** Examples.  *)
(*************************************************************************************)

Derive Functor for option.
Print option_functor.

Derive Functor for list.
Print list_functor.

Inductive tree A :=
  | Leaf : tree A
  | Node : A -> list (tree A) -> tree A.
Derive Functor for tree.
Print tree_functor.

Inductive tree' A :=
  | Leaf' : bool -> tree' A
  | Node' : A -> list (tree' (option A)) -> tree' A.
Derive Functor for tree'.
Print tree'_functor.