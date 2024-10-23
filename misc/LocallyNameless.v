(** * Locally nameless skeleton for MetaCoq. *)
From MetaCoq.Utils Require Import utils.
From MetaCoq.Template Require Import All.
From Coq Require String.

Import MCMonadNotation.

(** A convenient notation for function application, which saves many parentheses. *)
Notation "f $ x" := (f x) (at level 10, x at level 200, right associativity, only parsing).

(** * List utility functions not present in Coq's stdlib. *)
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

(** * MetaCoq utility functions. *)

(** [iterate n f x] applies [f] [n] times to [x]. *)
Fixpoint iterate {A} (n : nat) (f : A -> A) (x : A) : A :=
  match n with 
  | 0 => x
  | S n => iterate n f (f x)
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

(** * Named Contexts. *)

Module NContext.

(** A named context stores variable declarations indexed by identifiers [ident]. 
    We could use virtually anything in place of [ident],
    but this choice makes it easy to embed a variable in a term using [tVar]. 
    
    Introducing a declaration in the context shadows previous declarations with the same identifier.
*)
Record t := mk 
  { (** We store the [ident * context_decl] pairs in order, the most recent first. *)
    decls : list (ident * context_decl)
  ; (** The seed is used to generate fresh identifiers. *)
    seed : nat }.

(** The empty named context. *)
Definition empty : t := {| decls := [] ; seed := 0 |}.

(** Add a declaration to the context, shadowing previous declarations with the same identifier. *)
Definition push (id : ident) (decl : context_decl) (ctx : t) : t := 
  {| decls := (id, decl) :: ctx.(decls) ; seed := ctx.(seed) |}.

(** [fresh_ident basename ctx] builds a fresh identifier from [basename].
    It should be distinct from any other identifier constructed this way using [ctx]. *)
Definition fresh_ident (basename : string) (ctx : t) : ident * t :=
  let id := (basename ++ string_of_nat ctx.(seed) ++ "#")%bs in
  let ctx := {| decls := ctx.(decls) ; seed := ctx.(seed) + 1 |} in
  (id, ctx).

(** [get_decl id ctx] retrieves the most recent declaration for [id] in [ctx]. *)
Definition get_decl (id : ident) (ctx : t) : option context_decl :=
  List.find_map 
    (fun '(id', decl) => if id == id' then Some decl else None) 
    ctx.(decls).

(** Same as [get_decl] but returns only the type. *)
Definition get_type (id : ident) (ctx : t) : option term :=
  option_map decl_type (get_decl id ctx).

(** Same as [get_decl] but returns only the body. *)
Definition get_body (id : ident) (ctx : t) : option term :=
  decl_body =<< (get_decl id ctx).

End NContext.

(** * Locally nameless API. *)

(** Two very useful utility functions are [abstract] and [instantiate].
    These are used to *implement* locally nameless : users should not use them. *)

(** [abstract id t] replaces [tVar id] by [tRel 0] in [t]. *)
Definition abstract (id : ident) (t : term) : term := 
  let fix aux id depth t :=
    match t with 
    | tVar id' => if id == id' then tRel depth else t
    | _ => map_term_with_binders (Nat.add 1) (aux id) depth t
    end
  in 
  aux id 0 t.

(** [instantiate id t] replaces [tRel 0] by [tVar id] in [t]. *)
Definition instantiate (id : ident) (t : term) : term := 
  let fix aux id depth t :=
    match t with 
    | tRel n => if n == depth then tVar id else t
    | _ => map_term_with_binders (Nat.add 1) (aux id) depth t
    end
  in 
  aux id 0 t.

(** [with_local_decl decl ctx k] adds the local declaration [decl] to the named context [ctx] and 
    returns the continuation [k].

    The continuation has access to :
    - the extended context. 
    - the identifier of the added local variable. *)
Definition with_local_decl {T} (decl : context_decl) (ctx : NContext.t) (k : NContext.t -> ident -> T) : T :=
  (* Create a fresh identifier. *)
  let basename := string_of_name decl.(decl_name).(binder_name) in
  let (id, ctx) := NContext.fresh_ident basename ctx in 
  (* Pass the identifier and extended context to the continuation. *)
  k (NContext.push id decl ctx) id.

(** [mk_lambda name ty ctx body] creates a lambda abstraction in the locally nameless style.
    The body has access to an identifier and to an extended named context containing a declaration for this identifier.

    For instance here is how to create the identity function at type [T] :
      [mk_lambda name T ctx $ fun ctx x => tVar x]
*)
Definition mk_lambda (name : aname) (ty : term) (ctx : NContext.t) (mk_body : NContext.t -> ident -> term) : term :=
  with_local_decl {| decl_name := name ; decl_body := None ; decl_type := ty |} ctx $ fun ctx id => 
    let body := mk_body ctx id in
    tLambda name ty $ abstract id body.

(** You can implement similar functions to build other terms with binders. 
    For instance : *)
Definition mk_case 
  (ind : inductive) 
  (ctx : NContext.t) 
  (mk_pred : NContext.t -> list ident -> ident -> term) (** Build the predicate. The updated context contains the indices and the scrutinee. *) 
  (scrutinee : term) 
  (mk_branch : NContext.t -> list ident -> nat -> term) (** Build a branch for the constructor index. The arguments are in the updated context. *) 
  : term.
Admitted.

(** Then you also need to implement *destructors*. You can either :
    - use a *view* to implement pattern matching.
    - use *telescopes* if you already know what you want. 
*)
(** An example of a telescope : *)
Definition lambda_telescope {T} (t : term) (ctx : NContext.t) (k : NContext.t -> list ident -> T) : T.
Admitted.
(** Then [lambda_telescope (lambda x1. ... lambda xn. body) ctx k] 
    returns [k new_ctx [x1; ... ; xn]], where [new_ctx] is [ctx] with bindings for the 
    variables [x1] ... [xn]. *)
