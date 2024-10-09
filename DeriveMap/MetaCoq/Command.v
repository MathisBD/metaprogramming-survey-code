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

(** [lambda ctx name ty body] creates the lambda abstraction [fun name : ty => body].
    The body is passed an extended local context which contains a binding for [name : ty]. 
    
    This *does not* lift the body.
*)
Definition lambda {M : Type -> Type} {_ : Monad M} (ctx : context) (name : string) (ty : term) (mk_body : context -> M term) : M term := 
  let aname :=  {| binder_name := nNamed name ; binder_relevance := Relevant |} in
  let decl := {| decl_name := aname ; decl_type := ty ; decl_body := None |} in 
  mlet body <- mk_body (decl :: ctx) ;;
  ret $ tLambda aname ty body.

(** [arr t1 t2] constructs the non-dependent product [t1 -> t2]. It takes care of lifting [t2]. *)
Definition arrow (t1 : term) (t2 : term) : term := 
  tProd {| binder_name := nAnon ; binder_relevance := Relevant |} t1 (lift0 1 t2).

(****************************************************************************)
(** DeriveMap and AddMap commands. *)
(****************************************************************************)

Print case_info.

Section Commands.

Context (env : global_env).

Definition build_map (ctx : context) (ind : inductive) : TM term := 
  (* Abstract over the input parameters. *)
  (* TODO : actually ensure the level names are fresh. *)
  mlet uA <- tmQuoteUniverse ;;
  mlet uB <- tmQuoteUniverse ;;
  lambda ctx "A" (tSort $ sType uA) $ fun env => 
  lambda ctx "B" (tSort $ sType uB) $ fun env =>
  lambda ctx "f" (arrow (tRel 1) (tRel 0)) $ fun env =>
  lambda ctx "x" (tApp (tInd ind []) [tRel 2]) $ fun env =>
  (* Construct the case return clause. *)
  let ci := {| ci_ind := ind ; ci_npar := 1 ; ci_relevance := Relevant |} in
    tmReturn $ tRel 0.

(** DeriveMap command entry point. *)
Definition derive_map (ind_name : qualid) : TM unit := 
  (* Locate the inductive. *)
  mlet ind_ref <- tmLocate1 ind_name ;; 
  mlet ind <- 
    match ind_ref with 
    | IndRef ind => tmReturn ind
    | _ => tmFail "Provided constant is not an inductive." 
    end ;;
  (* Check the inductive has exactly one parameter. *)
  match lookup_inductive env ind with 
  | None => tmFail "lookup_inductive"
  | Some (_, ind_body) => tmReturn tt
    (*tmPrint ind_body.(ind_sort) ;;
    tmPrint (ind_realargs ind_body) ;;
    tmPrint ind_body.(ind_indices)*)
  end ;;
  (* Build the mapping function. We start with an empty context. *)
  mlet func <- build_map [] ind ;;
  tmPrint "The resulting function :" ;;
  tmPrint func ;;
  (* Add the mapping function to the global environment. *)
  (* TODO : handle the case where [ind_name] contains dots '.' *)
  tmMkDefinition (ind_name ++ "_map")%bs func ;;
  tmReturn tt.

End Commands.

About list.

Definition test : TM unit :=
  mlet (env, _) <- tmQuoteRec list ;;
  derive_map env "list".
MetaCoq Run test.