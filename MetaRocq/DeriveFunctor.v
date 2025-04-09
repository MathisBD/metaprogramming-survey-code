From Coq Require Import List.
(*From MetaCoq.Template Require Import All Checker.*)
From MetaCoq.Template Require Import Checker.

From MetaCoq.Utils Require Export
     monad_utils   (* Monadic notations *)
     MCUtils. (* Utility functions *)

From MetaCoq.Common Require Export
     uGraph        (* The graph of universes *)
     BasicAst      (* The basic AST structures *).

From MetaCoq.Template Require Export
     Ast           (* The term AST *)
     AstUtils      (* Utilities on the AST *)
     Induction     (* Induction *)
     LiftSubst     (* Lifting and substitution for terms *)
     UnivSubst     (* Substitution of universe instances *)
     Typing        (* Typing judgment *)
     TemplateMonad (* The TemplateMonad *)
     Loader        (* The plugin *)
     Lib           (* Meta-programming facilities *).

Import ListNotations MCMonadNotation.
Open Scope bs.

Existing Instance default_fuel.
Existing Instance config.default_checker_flags.

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
(** *** Utils.  *)
(*************************************************************************************)

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

(** [mk_letin ctx name def ty body] creates the let abstraction [let name : ty := def in body].
    The body is passed an extended local context which contains a binding for [name : ty := def]. 
    
    This *does not* lift the body.
*)
Definition mk_letin {M : Type -> Type} {_ : Monad M} (ctx : context) (name : string) (def : term) (ty : term) 
  (mk_body : context -> M term) : M term := 
  let aname :=  {| binder_name := nNamed name ; binder_relevance := Relevant |} in
  let decl := {| decl_name := aname ; decl_type := ty ; decl_body := Some def |} in 
  mlet body <- mk_body (decl :: ctx) ;;
  ret $ tLetIn aname def ty body.

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

(** [mk_kername path label] returns the kernel name with given directory path and label.
    For instance [mk_kername ["Coq" ; "Init" ; "Datatypes"] "nat"] builds the kername
    of the inductive type [nat]. *)
Definition mk_kername (path : list string) (label : string) : kername :=
  (MPfile $ List.rev path, label).    

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
  
(** [reduce_head F env ctx t] reduces [t] until a head constructor appears. *)
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
Definition dest_prod {T} (reducing := true) (env : global_env) (ctx : context) (t : term) 
  (k : context -> aname -> term -> term -> option T) : option T :=
  (* Weak head reduce [t] if needed. *) 
  match (if reducing then reduce_head env ctx t else Some t) with
  | None => None 
  | Some t =>
    (* Destruct the product. *)
    match t with 
    | tProd name ty body => 
      let decl := {| decl_name := name ; decl_type := ty ; decl_body := None |} in
      k (decl :: ctx) name ty body
    | _ => None
    end
  end.

(** [fresh_evar ctx] creates a fresh evar in context [ctx]. *)
Definition fresh_evar (ctx : context) : term :=
  let inst := mapi (fun i _ => tRel i) ctx in
  tEvar fresh_evar_id inst.

(*************************************************************************************)
(** *** Deriving.  *)
(*************************************************************************************)

(** Quote some terms we will need later. *)
MetaCoq Quote Definition quoted_fmap := (@fmap).
MetaCoq Quote Definition quoted_Functor := (@Functor).
MetaCoq Quote Definition quoted_Build_Functor := (@Build_Functor).

(** A small record to hold the inputs of the [fmap] function while
    we build its body. *)
Record inputs := mk_inputs { fmap' : nat ; A : nat ; B : nat ; f : nat ; x : nat }.

(** [lift_inputs n inp] lifts the inputs [inp] under [n] binders. *)
Definition lift_inputs (n : nat) (inp : inputs) : inputs :=
  {| fmap' := inp.(fmap') + n ; A := inp.(A) + n ; B := inp.(B) + n ; f := inp.(f) + n ; x := inp.(x) + n |}.

Definition build_arg (ctx : context) (inp : inputs) (arg : term) (arg_ty : term) : term :=
  (* If [A] does not occur in [arg_ty], no need to map. *)
  if noccur_between inp.(A) 1 arg_ty then arg
  (* Otherwise try to map over [arg_ty]. 
     We use an evar in place of the [Functor] instance, which gets solved later on. *)
  else
    let arg_ty' := replace_rel inp.(A) inp.(B) arg_ty in
    mkApps quoted_fmap 
      [ fresh_evar ctx 
      ; fresh_evar ctx 
      ; tRel inp.(A) 
      ; tRel inp.(B) 
      ; tRel inp.(f) 
      ; arg ].

Definition build_branch (ctx : context) (ind : inductive) 
  (inp : inputs) (ctor_idx : nat) (ctor : constructor_body) : branch term :=
  (* Get the context of the constructor. *)
  let bcontext := List.map decl_name ctor.(cstr_args) in 
  let n := List.length bcontext in
  (* Get the types of the arguments of the constructor at type [A]. *)
  let arg_tys := cstr_args_at ctor (tInd ind []) [tRel inp.(A)] in
  (* Process the arguments one by one, starting from the outermost one. *)
  let loop := fix loop ctx i acc decls :=
    match decls with 
    | [] => List.rev acc 
    | d :: decls => 
      let ctx := d :: ctx in
      (* We call build_arg at a depth which is consistent with the local contex,
         and we lift the result to bring it at depth [n]. *)
      let mapped_arg := build_arg ctx (lift_inputs (i + 1) inp) (tRel 0) (lift0 1 d.(decl_type)) in
      loop ctx (i + 1) (lift0 (n - i - 1) mapped_arg :: acc) decls 
    end
  in 
  (* The mapped arguments are at depth [n]. *)
  let mapped_args := loop ctx 0 [] (List.rev arg_tys) in
  (* Apply the constuctor to the mapped arguments. *)
  let bbody := tApp (tConstruct ind ctor_idx []) $ tRel (inp.(B) + n) :: mapped_args in
  (* Assemble the branch's context and body. *)
  mk_branch bcontext bbody.

Definition build_fmap (ctx : context) (ind : inductive) (ind_body : one_inductive_body) : term := 
  (* Create the type of the mapping function. *)
  let fmap_ty :=
    (mk_prod ctx "A" (tSort $ sType fresh_universe) $ fun ctx =>
    mk_prod ctx "B" (tSort $ sType fresh_universe) $ fun ctx =>
    ret (mk_arrow 
      (mk_arrow (tRel 1) (tRel 0))
      (mk_arrow (tApp (tInd ind []) [tRel 1]) (tApp (tInd ind []) [tRel 0]))))
  in
  (* Abstract over the input parameters. *)
  mk_fix ctx "fmap_rec" 3 fmap_ty $ fun ctx =>
  mk_lambda ctx "A" (tSort $ sType fresh_universe) $ fun ctx => 
  mk_lambda ctx "B" (tSort $ sType fresh_universe) $ fun ctx =>
  mk_lambda ctx "f" (mk_arrow (tRel 1) (tRel 0)) $ fun ctx =>
  mk_lambda ctx "x" (tApp (tInd ind []) [tRel 2]) $ fun ctx =>
  (* Build the recursive instance. *)
  let rec_inst := mkApps quoted_Build_Functor [ tInd ind [] ; tRel 4 ] in
  let rec_inst_ty := mkApps quoted_Functor [ tInd ind [] ] in
  mk_letin ctx "rec_inst" rec_inst rec_inst_ty $ fun ctx =>
  (* Gather the parameters. *)
  let inp := {| fmap' := 5 ; A := 4 ; B := 3 ; f := 2 ; x := 1 |} in
  (* Construct the case information. *)
  let ci := {| ci_ind := ind ; ci_npar := 1 ; ci_relevance := Relevant |} in
  (* Construct the case predicate. *)
  let pred := 
    {| puinst := []
    ;  pparams := [tRel inp.(A)]
    ;  pcontext := [{| binder_name := nNamed "x" ; binder_relevance := Relevant |}]
    ;  preturn := tApp (tInd ind []) [ tRel $ inp.(B) + 1 ] |}
  in
  (* Construct the branches. *)
  let branches := mapi (build_branch ctx ind inp) ind_body.(ind_ctors) in
  (* Finally make the case expression. *)
  tCase ci pred (tRel inp.(x)) branches.

(** DeriveFunctor command entry point. *)
Definition derive_functor {A} (raw_ind : A) : TM unit := 
  (* Locate the inductive. *)
  mlet (env, quoted_raw_ind) <- tmQuoteRec raw_ind ;;
  mlet ind <- 
    match quoted_raw_ind with 
    | tInd ind [] => ret ind
    | tInd ind _ => tmFail "Universe polymorphic inductives are not supported."
    | _ => tmFail "Expected an inductive."
    end
  ;; 
  (* Get the inductive body. *)
  mlet (ind_mbody, ind_body) <-
    match lookup_inductive env ind with 
    | None => tmFail "Could not lookup inductive"
    | Some bodies => tmReturn bodies 
    end
  ;;
  (* Check the inductive is non-mutual. *)
  if Nat.ltb 1 (List.length ind_mbody.(ind_bodies)) 
  then tmFail "Mutual inductives are not supported" else
  (* Check the inductive has exactly one parameter. *)
  if negb (ind_mbody.(ind_npars) == 1) 
  then tmFail "Only inductives with exactly one parameter are supported." else
  (* Build the mapping function. We start with an empty context. *)
  let func := build_fmap [] ind ind_body in
  (* Build the functor instance. *)
  let inst := mkApps quoted_Build_Functor [tInd ind [] ; func] in
  (* Unquote to solve evars (and resolve typeclasses).
     We also normalize the resulting term to help typeclass resolution. *)
  mlet fctor <- tmUnquoteTyped (Type -> Type) (tInd ind []) ;;
  mlet inst <- tmEval cbv =<< tmUnquoteTyped (Functor fctor) inst ;;
  (* Declare the instance. *)
  let inst_name := ind_body.(ind_name) ++ "_functor" in
  tmMkDefinition inst_name =<< tmQuote inst ;;
  mlet inst_ref <- tmLocate1 inst_name ;;
  tmExistingInstance export inst_ref.

(*************************************************************************************)
(** *** Examples.  *)
(*************************************************************************************)

Unset MetaCoq Strict Unquote Universe Mode.
Typeclasses eauto := (bfs).

MetaCoq Run (derive_functor option).
Print option_functor.

MetaCoq Run (derive_functor list).
Print list_functor.

Inductive tree A :=
  | Leaf : tree A
  | Node : A -> list (tree A) -> tree A.
MetaCoq Run (derive_functor tree).
Print tree_functor.

Inductive tree' A :=
  | Leaf' : bool -> A -> tree' A
  | Node' : list (tree' (option A)) -> tree' A.
MetaCoq Run (derive_functor tree').
Print tree'_functor.
