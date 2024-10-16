(* Locally nameless skeleton for MetaCoq. *)
From MetaCoq.Utils Require Import utils.
From MetaCoq.Template Require Import All.
From DeriveMap.MetaCoq Require Import Utils.
From Coq Require String.

Import MCMonadNotation.

(** A convenient notation for function application, which saves many parentheses. *)
Notation "f $ x" := (f x) (at level 10, x at level 200, right associativity, only parsing).


(*******************************************************************************)
(** List utility functions not present in Coq's stdlib. *)
(*******************************************************************************)
Module List.
Include List.

(** [find_map pred l] applies [pred] to each element in [l] in order, 
    and returns the first result of the form [Some _]. *)
Fixpoint find_map {A B} (pred : A -> option B) (l : list A) : option B :=
  match l with 
  | [] => None
  | hd :: tl => 
    match pred hd with 
    | None => find_map pred tl
    | Some res => Some res
    end
  end.

End List.

(*******************************************************************************)
(** This module defines named contexts which store variable declarations 
    indexed by identifiers [ident]. We could use virtually anything in place of identifiers,
    but this choice makes it easy to embed a variable in a term using [tVar]. 
    
    Introducing a declaration in the context shadows previous declarations with the same identifier.
*)
(*******************************************************************************)
Module NamedContext.

Record t := mk 
  { (* We store the [ident * declaration] pairs in order, the most recent first. 
       A more efficient implementation would perhaps use a map. *)
    decls : list (ident * context_decl)
  ; (* The seed is used to generate fresh identifiers. *)
    seed : nat }.

(** The empty named context. *)
Definition empty : t := {| decls := [] ; seed := 0 |}.

(** Add a declaration to the context, shadowing previous declarations with the same identifier. *)
Definition push (id : ident) (decl : context_decl) (ctx : t) : t := 
  {| decls := (id, decl) :: ctx.(decls) ; seed := ctx.(seed) |}.

(** [fresh_ident ctx basename] builds a fresh identifier from [basename].
    It should be distinct from any other identifier constructed this way using [ctx]. *)
Definition fresh_ident (ctx : t) (basename : string) : t * ident :=
  let id := (string_of_nat ctx.(seed) ++ "#" ++ basename)%bs in
  let ctx := {| decls := ctx.(decls) ; seed := ctx.(seed) + 1 |} in
  (ctx, id).

(** [get_decl id ctx] retrieves the most recent declaration for [id] in [ctx]. *)
Definition get_decl (id : ident) (ctx : t) : option context_decl :=
  List.find_map 
    (fun '(id', decl) => if id == id' then Some decl else None) 
    ctx.(decls).

(** Same as [get_decl] but returns only the type. *)
Definition get_type (id : ident) (ctx : t) : option term :=
  option_map decl_type (get_decl id ctx).

End NamedContext.

(*******************************************************************************)
(** A bare bones locally nameless API. *)
(*******************************************************************************)

Fixpoint abstract_aux (id : ident) (depth : nat) (t : term) : term :=
  match t with 
  | tVar id' => if id == id' then tRel depth else t
  | _ => map_term_with_binders (Nat.add 1) (abstract_aux id) depth t
  end.

(** [abstract id t] replaces [tVar id] by [tRel 0] in [t]. *)
Definition abstract (id : ident) (t : term) : term := abstract_aux id 0 t.

(** [with_local_decl decl ctx k] adds the local declaration [decl] to the named context [ctx] and 
    returns the continuation [k].

    The continuation has access to :
    - the extended context. 
    - the identifier of the added local variable. *)
Definition with_local_decl {T} (decl : context_decl) (ctx : NamedContext.t) (k : NamedContext.t -> ident -> T) : T :=
  (* Create a fresh identifier. *)
  let basename := string_of_name decl.(decl_name).(binder_name) in
  let (ctx, id) := NamedContext.fresh_ident ctx basename in 
  (* Pass the identifier and extended context to the continuation. *)
  k (NamedContext.push id decl ctx) id.

(** [mk_lambda name ty ctx body] creates a lambda abstraction in the locally nameless style.
    The body has access to an identifier and to an extended named context containing a declaration for this identifier.

    For instance here is how to create the identity function at type [T] :
      [mk_lambda name T ctx $ fun ctx x => tVar x]
*)
Definition mk_lambda (name : aname) (ty : term) (ctx : NamedContext.t) (mk_body : NamedContext.t -> ident -> term) : term :=
  with_local_decl {| decl_name := name ; decl_body := None ; decl_type := ty |} ctx $ fun ctx id => 
    let body := mk_body ctx id in
    tLambda name ty $ abstract id body.


(**Definition mk_case _ _ (mk_pred : ...) (mk_branch : NamedContext.t -> ctr -> list id -> term)*)


(** fun x : ty => body 
 
fresh id 
>> k (push id ty ctx) id body
*)
(**Definition dest_lambda (id, ty, body) (ctx : NamedContext.t) (k : NamedContext.t -> list id -> term (* body *) -> T) -> T *)

