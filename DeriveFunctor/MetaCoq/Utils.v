From Coq Require Import List.
From MetaCoq.Template Require Import All Pretty.
From MetaCoq Require Import Checker.
From MetaCoq.Utils Require Import monad_utils.

Import MCMonadNotation ListNotations.
Existing Instance default_fuel.
Existing Instance config.default_checker_flags.

(** A convenient notation for function application, which saves many parentheses. *)
Notation "f $ x" := (f x) (at level 10, x at level 200, right associativity, only parsing).

(** I write this a lot. *)
Notation TM := TemplateMonad.

(** [iterate n f x] applies [f] [n] times to [x]. *)
Fixpoint iterate {A} (n : nat) (f : A -> A) (x : A) : A :=
  match n with 
  | 0 => x
  | S n => iterate n f (f x)
  end.

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


(** [mk_lambda ctx name ty body] creates the lambda abstraction [fun name : ty => body].
    The body is passed an extended local context which contains a binding for [name : ty]. 
    
    This *does not* lift the body.
*)
Definition mk_lambda {M : Type -> Type} {_ : Monad M} (ctx : context) (name : string) (ty : term) (mk_body : context -> M term) : M term := 
  let aname :=  {| binder_name := nNamed name ; binder_relevance := Relevant |} in
  let decl := {| decl_name := aname ; decl_type := ty ; decl_body := None |} in 
  mlet body <- mk_body (decl :: ctx) ;;
  ret $ tLambda aname ty body.

(** [mk_prod ctx name ty body] creates the dependent product [forall name : ty, body].
    The body is passed an extended local context which contains a binding for [name : ty]. 
    
    This *does not* lift the body.
*)
Definition mk_prod {M : Type -> Type} {_ : Monad M} (ctx : context) (name : string) (ty : term) (mk_body : context -> M term) : M term := 
  let aname :=  {| binder_name := nNamed name ; binder_relevance := Relevant |} in
  let decl := {| decl_name := aname ; decl_type := ty ; decl_body := None |} in 
  mlet body <- mk_body (decl :: ctx) ;;
  ret $ tProd aname ty body.

(** [mk_arrow t1 t2] constructs the non-dependent product [t1 -> t2]. It takes care of lifting [t2]. *)
Definition mk_arrow (t1 : term) (t2 : term) : term := 
  tProd {| binder_name := nAnon ; binder_relevance := Relevant |} t1 (lift0 1 t2).

(**  [mk_fix ctx name rec_arg_idx ty body] makes a single fixpoint with the given parameters.
    - [name] is the name of the fixpoint parameter.
    - [rec_arg_idx] is the index of the (structurally) recursive argument, starting at [0].
    - [ty] is the type of the fixpoint parameter.
    - [body] is the body of the fixpoint, which has access to the extended environment.
      The body is not lifted.

    For instance to build the fixpoint [fix add (n : nat) (m : nat) {struct m} : nat := ...]
    one could use [mk_fix ctx "add" 1 '(nat -> nat -> nat) (fun ctx -> ...)].
*)
Definition mk_fix {M : Type -> Type} {_ : Monad M} (ctx : context) 
  (name : string) (rec_arg_idx : nat) (ty : term) (mk_body : context -> M term) : M term :=
  let aname := {| binder_name := nNamed name ; binder_relevance := Relevant |} in
  let decl := {| decl_name := aname ; decl_type := ty ; decl_body := None |} in
  mlet body <- mk_body (decl :: ctx) ;;
  let def := {| dname := aname ; dtype := ty ; dbody := body ; rarg := rec_arg_idx |} in
  ret $ tFix [def] 0. 
(* TODO show to Yannick : removing [0] in the last line gives a cryptic error message.
   This happens all the time when using monads in Coq. *)

(** [mk_kername path label] returns the kernel name with given directory path and label.
    For instance [mk_kername ["Coq" ; "Init" ; "Datatypes"] "nat"] builds the kername
    of the inductive type [nat]. *)
Definition mk_kername (path : list string) (label : string) : kername :=
  (MPfile $ List.rev path, label).    

(** Pretty print a term to a string. *)  
Definition pp_term (env : global_env) (ctx : context) (t : term) : string :=
  let decl_ident d : ident :=
    match d.(decl_name).(binder_name) with 
    | nNamed n => n 
    | nAnon => "_"%bs
    end
  in
  print_term (env, Monomorphic_ctx) (List.map decl_ident ctx) true t.

(** [cstr_args_at cstr ind params] gives the context for the arguments of the constructor [cstr],
    substituting [ind] for the inductive and [params] for the parameters of the constructor. *)
Definition cstr_args_at (cstr : constructor_body) (ind : term) (params : list term) : context :=
  subst_context (List.rev (ind :: params)) 0 $ cstr_args cstr.
    
(** [replace_rel a b t] replaces [Rel a] with [Rel b] in [t]. *)
Fixpoint replace_rel (a b : nat) (t : term) : term :=
  if t == tRel a
  then tRel b
  else map_term_with_binders (Nat.add 1) (replace_rel a) b t.

(** [subterm x t] checks whether [x] occurs in [t], modulo alpha equivalence.
    It takes time [O(size(x) * size(t))]. *)
Definition subterm (x t : term) : bool :=
  (* Hack : we only support the case where [x] is a [tRel]. This is sufficient for our purposes.
     For the general case we would need [fold_term_with_binders] and I'm too lazy to implement it. *)
  match x with 
  | tRel n => negb $ noccur_between n 1 t
  | _ => false 
  end. 
  
(** [reduce_head F env ctx t] reduces [t] until a head constructor appears.
    I think this does weak head normalization but I'm not completely sure. *)
Definition reduce_head `{F : Fuel} (env : global_env) (ctx : context) (t : term) : option term :=
  match t with
  | tLambda _ _ _ => Some t 
  | tProd _ _ _ => Some t
  | _ =>
    match hnf_stack env ctx t with 
    | Checked (f, args) => Some (mkApps f args) 
    | _ => None
    end
  end.

(* [dest_prod ctx t k] destructs [t] which should be of the form [tProd _ _ _],
   and passes the extended context and the product arguments to the continuation [k]. 

   If [t] is not a product it returns [None]. 
   Ideally we would use any monad [M] which can fail instead of [option].
*)
Definition dest_prod {T} (reducing := true) (env : global_env) (ctx : context) (t : term) (k : context -> aname -> term -> term -> option T) : option T :=
  (* Weak head reduce [t] if needed. *) 
  mlet t <- (if reducing then reduce_head env ctx t else Some t) ;;
  (* Destruct the product. *)
  match t with 
  | tProd name ty body => 
    let decl := {| decl_name := name ; decl_type := ty ; decl_body := None |} in
    k (decl :: ctx) name ty body
  | _ => None
  end.