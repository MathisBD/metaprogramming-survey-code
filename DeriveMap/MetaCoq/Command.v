From MetaCoq.Utils Require Import utils.
From MetaCoq.Template Require Import All.
Require String.

Import MCMonadNotation.
Notation TM := TemplateMonad.

(****************************************************************************)
(** Utility functions. *)
(****************************************************************************)

(** A convenient notation for function application, which saves many parentheses. *)
Notation "f $ x" := (f x) (at level 10, x at level 200, right associativity, only parsing).

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

(****************************************************************************)
(** DeriveMap and AddMap commands. *)
(****************************************************************************)

MetaCoq Test Quote (match [1] with [] => [] | hd :: tl => tl end).

Print constructor_body.

Section Commands.

Context (env : global_env).

Record params := mk_params { ind : inductive ; map : nat ; A : nat ; B : nat ; f : nat ; x : nat }.

Definition lift_params (n : nat) (p : params) : params :=
  {| ind := p.(ind) ; map := p.(map) + n ; A := p.(A) + n ; B := p.(B) + n ; f := p.(f) + n ; x := p.(x) + n |}.

Definition build_arg (ctx : context) (p : params) (arg : term) (arg_ty : term) : term :=
  arg.

Definition build_branch (ctx : context) (p : params) (ctor : constructor_body) : TM (branch term) :=
  tmPrint =<< tmEval cbv ctor.(cstr_args) ;;
  (* Get the context of the constructor. *)
  let bcontext := List.map decl_name ctor.(cstr_args) in 
  let n := List.length bcontext in
  (* Process the arguments one by one, starting from the outermost one. *)
  let loop := fix loop ctx i acc decls :=
    match decls with 
    | [] => List.rev acc 
    | d :: decls => 
      let ctx := d :: ctx in
      (* We call build_arg at a depth which is consistent with the local context of the environment,
         and we lift the result to bring it at depth [n]. *)
      let mapped_arg := build_arg ctx (lift_params (i + 1) p) (tRel 0) (lift0 1 d.(decl_type)) in
      loop ctx (i + 1) (lift0 (n - i - 1) mapped_arg :: acc) decls 
    end
  in 
  (* The mapped arguments are at depth [n]. *)
  let mapped_args := loop ctx 0 [] $ List.rev ctor.(cstr_args) in
  (* Apply the constuctor to the mapped arguments. *)
  let bbody := tApp (tInd p.(ind) []) $ tRel (p.(B) + n) :: mapped_args in
  (* Assemble the branch's context and body. *)
  tmReturn $ mk_branch bcontext bbody.

#[using="All"]
Definition build_map (ctx : context) (ind : inductive) (ind_body : one_inductive_body) : TM term := 
  (* Create some universes for the types of A and B. *)
  mlet uA <- tmQuoteUniverse ;;
  mlet uB <- tmQuoteUniverse ;;
  (* Create the type of the mapping function. *)
  mlet map_ty <-
    (mk_prod ctx "A" (tSort $ sType uA) $ fun ctx =>
    mk_prod ctx "B" (tSort $ sType uB) $ fun ctx =>
    ret (mk_arrow 
      (mk_arrow (tRel 1) (tRel 0))
      (mk_arrow (tApp (tInd ind []) [tRel 1]) (tApp (tInd ind []) [tRel 0]))))
  ;;
  (* Abstract over the input parameters. *)
  mk_fix ctx "map" 3 map_ty $ fun ctx =>
  mk_lambda ctx "A" (tSort $ sType uA) $ fun ctx => 
  mk_lambda ctx "B" (tSort $ sType uB) $ fun ctx =>
  mk_lambda ctx "f" (mk_arrow (tRel 1) (tRel 0)) $ fun ctx =>
  mk_lambda ctx "x" (tApp (tInd ind []) [tRel 2]) $ fun ctx =>
  (* Gather the parameters. *)
  let p := {| ind := ind ; map := 4 ; A := 3 ; B := 2 ; f := 1 ; x := 0 |} in
  (* Construct the case information. *)
  let ci := {| ci_ind := ind ; ci_npar := 1 ; ci_relevance := Relevant |} in
  (* Construct the case predicate. *)
  let pred := 
    {| puinst := []
    ;  pparams := [tRel 3]
    ;  pcontext := [{| binder_name := nNamed "x" ; binder_relevance := Relevant |}]
    ;  preturn := tApp (tInd ind []) [tRel 2] |}
  in
  (* Construct the branches. *)
  mlet branches <- monad_map (build_branch ctx p) ind_body.(ind_ctors) ;;
  (* Finally make the case expression. *)
  tmReturn (tCase ci pred (tRel 0) branches).

End Commands.

(** DeriveMap command entry point. *)
Definition derive_map (ind_name : qualid) : TM unit := 
  (* Locate the inductive. *)
  mlet ind_ref <- tmLocate1 ind_name ;; 
  mlet ind <- 
    match ind_ref with 
    | IndRef ind => tmReturn ind
    | _ => tmFail "Provided constant is not an inductive." 
    end ;;
  (* Get the environment needed to build the mapping function. *)
  mlet ind_term <- tmUnquote (tInd ind []) ;;
  mlet (env, _) <- tmQuoteRec (my_projT2 ind_term) ;;
  (* Get the inductive body. *)
  mlet ind_body <-
    match lookup_inductive env ind with 
    | None => tmFail "lookup_inductive"
    | Some (_, ind_body) => tmReturn ind_body 
    end
  ;;
  (* Check the inductive has exactly one parameter. *)
  let n_params := ind_realargs ind_body - List.length (ind_indices ind_body) in 
  (if n_params == 1 then tmReturn tt
  else tmFail "Provided inductive should have exactly one parameter.")
  ;;
  (* Build the mapping function. We start with an empty context. *)
  mlet func <- build_map env [] ind ind_body ;;
  tmPrint "The resulting function :" ;;
  tmPrint =<< tmEval cbv func ;;
  (* Add the mapping function to the global environment. *)
  (* TODO : handle the case where [ind_name] contains dots '.' *)
  tmMkDefinition (ind_name ++ "_map")%bs func ;;
  tmReturn tt.

MetaCoq Run (derive_map "list").

Print eq.

Print tmPrint.