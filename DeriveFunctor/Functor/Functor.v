(** This file defines a standard [Functor] typeclass. *)

Class Functor (F : Type -> Type) : Type :=
{
  fmap {A B} : (A -> B) -> F A -> F B
}.

(** The identity function is a functor. *)
Definition Id (A : Type) := A.
#[export] Instance functor_id : Functor Id := { fmap _ _ f a := f a }.

(** Composition of functors is still a functor. *)
#[export] Instance functor_comp F G `(Functor F) `(Functor G) : Functor (fun T => G (F T)) :=
{ fmap _ _ f := @fmap G _ _ _ (@fmap F _ _ _ f) }.
