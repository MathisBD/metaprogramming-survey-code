From MetaCoq.Utils Require Import utils.
From MetaCoq.Template Require Import All Pretty.
From MetaCoq Require Import Checker.
From DeriveMap.MetaCoq Require Import Utils.
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

(** [conv env ctx t1 t2] checks whether [t1] and [t2] are convertible in local context [ctx]. *)
Definition conv env ctx (t1 : term) (t2 : term) : bool :=
  match @check_conv config.default_checker_flags default_fuel env init_graph ctx t1 t2 with 
  | Checked _ => true 
  | TypeError _ => false 
  end.

(** [alpha_eq t1 t2] checks if [t1] and [t2] are equal modulo alpha conversion. *)
Definition alpha_eq (t1 : term) (t2 : term) : bool :=
  @eq_term config.default_checker_flags init_graph t1 t2.

(** Pretty print a term to a string. *)  
Definition pp_term (env : global_env) (ctx : context) (t : term) : string :=
  let decl_ident d : ident :=
    match d.(decl_name).(binder_name) with 
    | nNamed n => n 
    | nAnon => "_"
    end
  in
  print_term (env, Monomorphic_ctx) (List.map decl_ident ctx) true t.

(** This is the corrected version of [noccur_between].
    [correct_noccur_between k n t] checks that [t] does *not* contain any de Bruijn index
    in the range [k ... k + n - 1]. *)
Fixpoint correct_noccur_between (k n : nat) (t : term) {struct t} : bool :=
  match t with
  | tRel i => (i <? k) || (k + n <=? i)
  | tEvar _ args => forallb (correct_noccur_between k n) args
  | tCast c _ t0 => correct_noccur_between k n c && correct_noccur_between k n t0
  | tProd _ T M | tLambda _ T M =>
	  correct_noccur_between k n T && correct_noccur_between (S k) n M
  | tLetIn _ b t0 b' =>
      correct_noccur_between k n b && correct_noccur_between k n t0 &&
      correct_noccur_between (S k) n b'
  | tApp u v => correct_noccur_between k n u && forallb (correct_noccur_between k n) v
  | tCase _ p c brs =>
      let k' := #|pcontext p| + k in
      let p' :=
        test_predicate (fun _ : Instance.t => true) 
          (correct_noccur_between k n) (correct_noccur_between k' n) p in
      let brs' := test_branches_k (fun k0 : nat => correct_noccur_between k0 n) k brs
        in
      p' && correct_noccur_between k n c && brs'
  | tProj _ c => correct_noccur_between k n c
  | tFix mfix _ | tCoFix mfix _ =>
      let k' := #|mfix| + k in
      forallb (test_def (correct_noccur_between k n) (correct_noccur_between k' n)) mfix
  | tArray _ arr def ty =>
      forallb (correct_noccur_between k n) arr && correct_noccur_between k n def &&
      correct_noccur_between k n ty
  | _ => true
  end.

(** [cstr_args_at cstr ind params] gives the context for the arguments of the constructor [cstr],
    substituting [ind] for the inductive and [params] for the parameters of the constructor. *)
Definition cstr_args_at (cstr : constructor_body) (ind : term) (params : list term) : context :=
  subst_context (List.rev (ind :: params)) 0 $ cstr_args cstr.

(** [monad_mapi f l] is the same as [monad_map f l] except the function [f]
    is fed the index of each argument. *)
Definition monad_mapi (T : Type -> Type) (M : Monad T) (A B : Type) (f : nat -> A -> T B) (l : list A) :=
  monad_map (fun '(i, a) => f i a) $ mapi pair l.

Arguments monad_mapi {T}%_function_scope {M} {A B}%_type_scope f%_function_scope l%_list_scope.
    
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
  | tRel n => negb $ correct_noccur_between n 1 t
  | _ => false 
  end. 
  
(****************************************************************************)
(** Lifting mapping functions. *)
(****************************************************************************)

(** This module handles lifting of functions from basic types to more elaborate types. *)
Module Lift.

(** A lifting problem consists in lifting a function [f : A -> B] to a function [T -> U].
    It is assumed that U is equal to T with A replaced by B. *)
Record problem := mk_problem 
  { lp_A : term ; lp_B : term ; lp_f : term ; lp_T : term ; lp_U : term }.

(** A lifting rule takes as input a lifting problem, and either :
    - Fails by returning [None]
    - Succeeds by returning a function [Some f'] where [f' : T -> U].
*)
Definition rule := global_env -> context -> problem -> option term.

(** Basic lifting rule when [T] = [A].
    In this case we solve with [f' = f] *)
Definition apply_rule : rule := 
  fun env ctx lp =>
    if conv env ctx lp.(lp_A) lp.(lp_T)
    then Some lp.(lp_f)
    else None.

(** Basic lifting rule when [A] does not occur in [T].
    In this case we solve with [f' x = x]. *)
Definition id_rule : rule :=
  fun env ctx lp =>
    if subterm lp.(lp_A) lp.(lp_T)
    then None 
    else Some $ mk_lambda ctx "x" lp.(lp_T) (fun ctx => tRel 0).

(** [mzero] is a lifting rule which always fails. *)
Definition mzero : rule :=
  fun env ctx lp => None.

(** [msum r1 r2] tries the rule [r1], and if it fails applies [r2]. *)
Definition msum (r1 : rule) (r2 : rule) : rule :=
  fun env ctx lp => 
    match r1 env ctx lp with
    | None => r2 env ctx lp 
    | Some res => Some res
    end.

(** [sequence rs] combines the lifting rules [rs] by trying them out in order from first to last
    until one succeeds. *)
Definition sequence (rs : list rule) : rule :=
  match rs with [] => mzero | r :: rs => List.fold_left msum rs r end.
  
(** Fixpoints for rules. We are in Coq so we use a [fuel] argument to prevent infinite recursion. *)
Fixpoint fix_rule (fuel : Fuel) (f : rule -> rule) : rule := 
  fun env ctx lp => 
    match fuel with 
    | 0 => None 
    | S fuel => f (fix_rule fuel f) env ctx lp
    end.

End Lift.

(****************************************************************************)
(** DeriveMap and AddMap commands. *)
(****************************************************************************)

(** A small record to hold the parameters of the mapping function while
    we build its body. *)
Record params := mk_params { ind : inductive ; map : nat ; A : nat ; B : nat ; f : nat ; x : nat }.

(** [lift_params n params] lifts the parameters [params] under [n] binders. *)
Definition lift_params (n : nat) (p : params) : params :=
  {| ind := p.(ind) ; map := p.(map) + n ; A := p.(A) + n ; B := p.(B) + n ; f := p.(f) + n ; x := p.(x) + n |}.

Definition build_arg env (ctx : context) (p : params) (arg : term) (arg_ty : term) : TM term :=
  tmPrint "ARG" ;;
  (* Build the lifting problem. *)
  let lp := Lift.mk_problem
    (tRel p.(A))
    (tRel p.(B))
    (tRel p.(f))
    arg_ty 
    (replace_rel p.(A) p.(B) arg_ty)
  in
  tmPrint =<< tmEval cbv lp ;;
  (* Build the lifting rule. *)
  let map_rule : Lift.rule :=
    fun env ctx lp =>
      if conv env ctx lp.(Lift.lp_T) $ tApp (tInd p.(ind) []) [tRel p.(A)]
      then Some $ tApp (tRel p.(map)) [tRel p.(A); tRel p.(B); tRel p.(f)]
      else None 
  in
  let rule := Lift.sequence [ Lift.apply_rule ; Lift.id_rule ; map_rule ] in
  (* Solve the lifting problem. *)
  match rule env ctx lp with 
  | None =>
    (* No applicable rule. *)
    tmFail ("No applicable rule for " ++ pp_term env ctx arg_ty)%bs
  | Some f' =>
    (* Success ! Apply [f'] to the argument. *) 
    tmReturn $ tApp f' [arg]
  end.

Definition build_branch env (ctx : context) (p : params) (ctor_idx : nat) (ctor : constructor_body) : TM (branch term) :=
  tmPrint "BRANCH" ;;
  (* Get the context of the constructor. *)
  let bcontext := List.map decl_name ctor.(cstr_args) in 
  let n := List.length bcontext in
  (* Get the types of the arguments of the constructor at type [A]. *)
  let arg_tys := cstr_args_at ctor (tInd p.(ind) []) [tRel p.(A)] in
  tmPrint =<< tmEval cbv arg_tys ;; 
  (* Process the arguments one by one, starting from the outermost one. *)
  let loop := fix loop ctx i acc decls :=
    match decls with 
    | [] => tmReturn $ List.rev acc 
    | d :: decls => 
      let ctx := d :: ctx in
      (* We call build_arg at a depth which is consistent with the local context of the environment,
         and we lift the result to bring it at depth [n]. *)
      mlet mapped_arg <- build_arg env ctx (lift_params (i + 1) p) (tRel 0) (lift0 1 d.(decl_type)) ;;
      loop ctx (i + 1) (lift0 (n - i - 1) mapped_arg :: acc) decls 
    end
  in 
  (* The mapped arguments are at depth [n]. *)
  mlet mapped_args <- loop ctx 0 [] (List.rev arg_tys) ;;
  (* Apply the constuctor to the mapped arguments. *)
  let bbody := tApp (tConstruct p.(ind) ctor_idx []) $ tRel (p.(B) + n) :: mapped_args in
  (* Assemble the branch's context and body. *)
  tmReturn $ mk_branch bcontext bbody.

Definition build_map env (ctx : context) (ind : inductive) (ind_body : one_inductive_body) : TM term := 
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
    ;  pparams := [tRel p.(A)]
    ;  pcontext := [{| binder_name := nNamed "x" ; binder_relevance := Relevant |}]
    ;  preturn := tApp (tInd ind []) [tRel $ p.(B) + 1 ] |}
  in
  (* Construct the branches. *)
  mlet branches <- monad_mapi (build_branch env ctx p) ind_body.(ind_ctors) ;;
  (* Finally make the case expression. *)
  tmReturn (tCase ci pred (tRel p.(x)) branches).

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

Inductive double A := 
  | Dnil : bool -> double A
  | Double : double A -> A -> double A.

MetaCoq Run (derive_map "double").

Print double_map.

(*Definition double_map :=
  fun (A B : Type) (f : A -> B) (x : double A) =>
  match x with 
  | Double x1 x2 => @Double B (f x1) (f x2)
  end.*)


(*MetaCoq Run (derive_map "double").

Print double_map.*)
