
(** A convenient notation for function application, which saves many parentheses. *)
Notation "f $ x" := (f x) (at level 10, x at level 100, right associativity, only parsing).

Module STLC.

(** * Simply typed lambda calculus. *)

Inductive ty :=
  | A0 : ty
  | A1 : ty 
  | A2 : ty
  | A3 : ty
  | Arrow : ty -> ty -> ty.

Inductive ctx := 
  | Empty : ctx 
  | Extend : ctx -> ty -> ctx.

Notation "c ,, t" := (Extend c t) (at level 60).

Inductive var : ctx -> ty -> Type := 
  | NewVar ctx ty : var (ctx ,, ty) ty
  | Weaken ty' {ctx ty} : var ctx ty -> var (ctx ,, ty') ty.

(* A context with atomic types. *)
Definition c := Empty ,, A3 ,, A2 ,, A1 ,, A0.

Definition v0 : var c A0 := 
  NewVar (Empty ,, A3 ,, A2 ,, A1) A0.

Definition v1 : var c A1 := 
  Weaken A0 $ NewVar (Empty ,, A3 ,, A2) A1.

Definition v2 : var c A2 :=
  Weaken A0 $ Weaken A1 $ NewVar (Empty ,, A3) A2.

Definition v0' : var (c ,, A3) A0 := Weaken A3 v0.

(* Explicitly typed terms. *)
Inductive tterm : ctx -> ty -> Type :=
  | tVar {ctx ty} : var ctx ty -> tterm ctx ty
  | tLamba {ctx t1 t2} : tterm (ctx ,, t1) t2 -> tterm ctx (Arrow t1 t2)
  | tApp {ctx t1 t2} : tterm ctx (Arrow t1 t2) -> tterm ctx t1 -> tterm ctx t2.
  
End STLC.

(** * Now the dependent version ! *)

Module CC.

(** Contexts abstract over [t] the type of terms. *)
Inductive ctx t : Type := 
  | Empty : ctx t
  | Push : ctx t -> t -> ctx t.

Inductive tterm : ctx tterm -> tterm -> Type := .

End CC.