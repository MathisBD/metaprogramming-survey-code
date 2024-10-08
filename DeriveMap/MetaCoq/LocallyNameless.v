(* Distributed under the terms of the MIT license. *)
From MetaCoq.Utils Require Import utils.
From MetaCoq.Template Require Import All.

Import MCMonadNotation.

(** A convenient notation for function application, which saves many parentheses. *)
Notation "f $ x" := (f x) (at level 10, x at level 200, right associativity, only parsing).

(** [iterate n f x] applies [f] [n] times to [x]. *)
Fixpoint iterate {A}  (n : nat) (f : A -> A) (x : A) : A :=
  match n with 
  | 0 => x
  | S n => iterate n f (f x)
  end.

(*******************************************************************************)
(** Open recursors on terms (which should be part of MetaCoq). *)
(*******************************************************************************)

Definition map_def (f : term -> term) (d : def term) : def term :=
  {| dname := d.(dname) ; dtype := f d.(dtype) ; dbody := f d.(dbody) ; rarg := d.(rarg) |}.

Definition map_predicate (f : term -> term) (p : predicate term) : predicate term :=
  {| puinst := p.(puinst) 
  ;  pparams := List.map f p.(pparams) 
  ;  pcontext := p.(pcontext)
  ;  preturn := f p.(preturn) |}.

Definition map_branch (f : term -> term) (b : branch term) : branch term := 
  {| bcontext := b.(bcontext) ; bbody := f b.(bbody) |}.

(** [map_term f t] maps [f] on the immediate subterms of [t].
    It is not recursive and the order with which subterms are processed is not specified. *)
Definition map_term (f : term -> term) (t : term) : term := 
  match t with
  | tRel _ | tVar _ | tSort _ | tConst _ _ | tInd _ _ | tConstruct _ _ _ | tInt _ | tFloat _ | tString _ => t
  | tEvar n ts => tEvar n (List.map f ts)
  | tCast b k t => tCast (f b) k (f t)
  | tProd name ty body => tProd name (f ty) (f body)
  | tLambda name ty body => tLambda name (f ty) (f body)
  | tLetIn name def ty body => tLetIn name (f def) (f ty) (f body)
  | tApp func args => tApp (f func) (List.map f args)
  | tProj proj t => tProj proj (f t)
  | tFix defs i => tFix (List.map (map_def f) defs) i
  | tCoFix defs i => tCoFix (List.map (map_def f) defs) i
  | tCase ci pred x branches => tCase ci (map_predicate f pred) (f x) (List.map (map_branch f) branches)
  | tArray l t def ty => tArray l (List.map f t) (f def) (f ty)
  end.

Definition map_predicate_with_binders {A} (lift : A -> A) (f : A -> term -> term) (acc : A) (p : predicate term) : predicate term :=
  let acc_return := iterate (List.length p.(pcontext)) lift acc in
  {| puinst := p.(puinst) 
  ;  pparams := List.map (f acc) p.(pparams) 
  ;  pcontext := p.(pcontext)
  ;  preturn := f acc_return p.(preturn) |}.

Definition map_branch_with_binders {A} (lift : A -> A) (f : A -> term -> term) (acc : A) (b : branch term) : branch term := 
  let acc_body := iterate (List.length b.(bcontext)) lift acc in
  {| bcontext := b.(bcontext) ; bbody := f acc_body b.(bbody) |}.

(** [map_term_with_binders lift f acc t] maps [f acc] on the immediate subterms of [t].
    It carries an extra data [acc] (typically a lift index) which is processed by [lift] 
    (which typically add 1 to [acc]) at each binder traversal.
    It is not recursive and the order with which subterms are processed is not specified. *)
Definition map_term_with_binders {A} (lift : A -> A) (f : A -> term -> term) (acc : A) (t : term) : term :=
  match t with
  | tRel _ | tVar _ | tSort _ | tConst _ _ | tInd _ _ | tConstruct _ _ _ | tInt _ | tFloat _ | tString _ => t
  | tEvar n ts => tEvar n (List.map (f acc) ts)
  | tCast b k t => tCast (f acc b) k (f acc t)
  | tProd name ty body => tProd name (f acc ty) (f (lift acc) body)
  | tLambda name ty body => tLambda name (f acc ty) (f (lift acc) body)
  | tLetIn name def ty body => tLetIn name (f acc def) (f acc ty) (f (lift acc) body)
  | tApp func args => tApp (f acc func) (List.map (f acc) args)
  | tProj proj t => tProj proj (f acc t)
  (* For [tFix] and [tCoFix] we have to take care to lift the accumulator 
     only when processing the body of the (co)fixpoint. *)
  | tFix defs i => 
    let acc_body := iterate (List.length defs) lift acc in
    let map_def d := 
      {| dname := d.(dname) ; dtype := f acc d.(dtype) ; dbody := f acc_body d.(dbody) ; rarg := d.(rarg) |}
    in
    tFix (List.map map_def defs) i
  | tCoFix defs i => 
    let acc_body := iterate (List.length defs) lift acc in
    let map_def d := 
      {| dname := d.(dname) ; dtype := f acc d.(dtype) ; dbody := f acc_body d.(dbody) ; rarg := d.(rarg) |}
    in
    tCoFix (List.map map_def defs) i
  | tCase ci pred x branches => 
    tCase ci (map_predicate_with_binders lift f acc pred) (f acc x) (List.map (map_branch_with_binders lift f acc) branches)
  | tArray l t def ty => tArray l (List.map (f acc) t) (f acc def) (f acc ty)
  end.

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
(** This module defines named contexts, i.e. local contexts which store
    named assumptions or definitions. *)
(*******************************************************************************)
Module NamedContext.

Record t := mk { decls : list (ident * context_decl) }.

Definition empty : t := {| decls := [] |}.

Definition push (id : ident) (decl : context_decl) (ctx : t) : t := 
  {| decls := (id, decl) :: ctx.(decls) |}.

Definition get_decl (id : ident) (ctx : t) : option context_decl :=
  List.find_map 
    (fun '(id', decl) => if id == id' then Some decl else None) 
    ctx.(decls).

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
  let id := "TODO" in 
  (* Pass the identifier and extended context to the continuation. *)
  k (NamedContext.push id decl ctx) id.

(** [mk_lambda name ty ctx body] creates a lambda abstraction in the locally nameless style.
    The body has access to an identifier and to an extended named context containing a declaration for this identifier.

    For instance here is how to create the identity function at type [T] :
      [mk_lambda xname T ctx $ fun ctx x => tVar x]
*)
Definition mk_lambda (name : aname) (ty : term) (ctx : NamedContext.t) (mk_body : NamedContext.t -> ident -> term) : term :=
  withLocalDecl {| decl_name := name ; decl_body := None ; decl_type := ty |} ctx $ fun ctx id => 
    let body := mk_body ctx id in
    tLambda name ty $ abstract id body.