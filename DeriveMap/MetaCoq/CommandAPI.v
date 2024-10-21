From MetaCoq.Utils Require Import utils.
From MetaCoq.Template Require Import All Pretty.
From MetaCoq Require Import Checker.
From DeriveMap.MetaCoq Require Import Utils.
From ReductionEffect Require Import PrintingEffect.
From DeriveMap.MetaCoq Require Import API.
Require String.

Import MCMonadNotation.
Notation TM := TemplateMonad.

Set Universe Polymorphism.

Existing Instance config.default_checker_flags.
Existing Instance default_fuel.

(****************************************************************************)
(** Utility functions. *)
(****************************************************************************)

(** A convenient notation for function application, which saves many parentheses. *)
Notation "f $ x" := (f x) (at level 10, x at level 200, right associativity, only parsing).

(** [get_rel x state] returns the de Bruijn index of variable [x] in [state]. *)
Definition get_rel (x : ident) (s : state) : nat :=
  fst $ get_idecl x s.

(** [mk_arrow t1 t2] constructs the non-dependent product [t1 -> t2]. It takes care of lifting [t2]. *)
Definition mk_arrow (t1 : term) (t2 : term) : term := 
  tProd {| binder_name := nAnon ; binder_relevance := Relevant |} t1 (lift0 1 t2).

(** Pretty print a term to a string. *)  
Definition pp_term (env : global_env) (ctx : context) (t : term) : string :=
  let decl_ident d : ident :=
    match d.(decl_name).(binder_name) with 
    | nNamed n => n 
    | nAnon => "_"
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
Definition rule := global_env -> state -> problem -> option term.

(** Basic lifting rule when [T] = [A].
    In this case we solve with [f' = f] *)
Definition apply_rule : rule := 
  fun env state lp =>
    let ctx := get_typing_context state in
    let () := print ("RULE apply ON", pp_term env ctx lp.(lp_T)) in
    if check_conv env init_graph ctx lp.(lp_A) lp.(lp_T)
    then let () := print ">>SUCCESS" in Some lp.(lp_f)
    else let () := print ">>FAIL" in None.

(** Basic lifting rule when [A] does not occur in [T].
    In this case we solve with [f' x = x]. *)
Definition id_rule : rule :=
  fun env state lp =>
    let ctx := get_typing_context state in
    let () := print ("RULE id ON", pp_term env ctx lp.(lp_T)) in
    if subterm lp.(lp_A) lp.(lp_T)
    then let () := print ">>FAIL" in None 
    else 
      let () := print ">>SUCCESS" in 
      let binder := {| binder_name := nNamed "x" ; binder_relevance := Relevant |} in
      Some $ kp_tLambda binder lp.(lp_T) None state (fun x state => tRel $ get_rel x state).

(** [mzero] is a lifting rule which always fails. *)
Definition mzero : rule :=
  fun env state lp => None.

(** [msum r1 r2] tries the rule [r1], and if it fails applies [r2]. *)
Definition msum (r1 : rule) (r2 : rule) : rule :=
  fun env state lp => 
    match r1 env state lp with
    | None => r2 env state lp 
    | Some res => Some res
    end.

(** [sequence rs] combines the lifting rules [rs] by trying them out in order from first to last
    until one succeeds. *)
Definition sequence (rs : list rule) : rule :=
  match rs with [] => mzero | r :: rs => List.fold_left msum rs r end.
  
(** Fixpoints for rules. We are in Coq so we use a [fuel] argument to prevent infinite recursion. *)
Fixpoint fix_rule `{fuel : Fuel} (f : rule -> rule) : rule := 
  fun env state lp => 
    match fuel with 
    | 0 => None 
    | S fuel => f (@fix_rule fuel f) env state lp
    end.

End Lift.

(****************************************************************************)
(** DeriveMap and AddMap commands. *)
(****************************************************************************)

(** A small record to hold the parameters of the mapping function while
    we build its body. *)
Record params := mk_params { ind : inductive ; map : ident ; A : ident ; B : ident ; f : ident ; x : ident }.

Definition build_arg env (state : state) (p : params) (arg : term) (arg_ty : term) : TM term :=
  tmPrint "ARG" ;;
  (* Build the lifting problem. *)
  let lp := Lift.mk_problem
    (tRel $ get_rel p.(A) state)
    (tRel $ get_rel p.(B) state)
    (tRel $ get_rel p.(f) state)
    arg_ty 
    (replace_rel (get_rel p.(A) state) (get_rel p.(B) state) arg_ty)
  in
  (* Build the lifting rule. *)
  (*let map_rule : Lift.rule :=
    fun env ctx lp =>
      if check_conv env init_graph ctx lp.(Lift.lp_T) $ tApp (tInd p.(ind) []) [tRel p.(A)]
      then Some $ tApp (tRel p.(map)) [tRel p.(A); tRel p.(B); tRel p.(f)]
      else None 
  in*)
  let rule := Lift.sequence $ Lift.apply_rule :: Lift.id_rule :: [] in
  (* Solve the lifting problem. *)
  (* The use of [tmEval] is a hack to make [PrintEffect.print] actually print stuff. *)
  mlet res <- tmEval cbv (rule env state lp) ;;
  match res with 
  | None =>
    (* No applicable rule. *)
    tmFail ("No applicable rule for " ++ pp_term env (get_typing_context state) arg_ty)%bs
  | Some f' =>
    (* Success ! Apply [f'] to the argument. *) 
    tmReturn $ tApp f' [arg]
  end.

Print constructor_body.

(** [prod_telescope (forall x_1 : T_1, ..., forall x_n : T_n, body) state k]
    adds a declaration [id_i : decl_i] in [state] for each [x_i],
    and returns [k [id_1; ... ; id_n] body new_state].
    
    This assumes [body] is not itself a product, i.e. it peels off the maximal number of products. *)
Definition prod_telescope {T} (t : term) (st : state) (k : list ident -> term -> state -> T) : T :=
  let fix loop ids t st :=
    match t with 
    | tProd binder ty body => 
      let id := fresh_ident None st in
      loop (id :: ids) body (add_fresh_var id (mkdecl binder None ty) st)
    | body => k ids body st
    end
  in loop [] t st.

(** [instantiate_prod x (forall _, body)] returns [body] with [tRel 0] replaced by [x]. *)
Definition instantiate_prod (x : term) (t : term) : term :=
  match t with 
  | tProd _ _ body => subst0 [x] body
  | _ => t
  end.

Definition build_branch env (st : state) (p : params) (ctor_idx : nat) (ctor : constructor_body) : TM (branch term) :=
  tmPrint "BRANCH" ;;
  let n := List.length ctor.(cstr_args) in
  (* Get the type of the constructor for parameter [A]. *)
  let ctor_ty := instantiate_prod (tRel $ get_rel p.(A) st) ctor.(cstr_type) in
  (* Get access to the arguments. *)
  prod_telescope ctor_ty st $ fun args _ st =>
    (* Process each argument individually. *)
    mlet mapped_args <-
      monad_map (fun arg => build_arg env st p (tRel $ get_rel arg st) (get_one_type arg st)) args
    ;;
    (* Apply the constuctor to the mapped arguments. *)
    let bbody := tApp (tConstruct p.(ind) ctor_idx []) ((tRel $ get_rel p.(B) st) :: mapped_args) in
    (* Assemble the branch's context and body. *)
    tmReturn $ mk_branch (List.map decl_name ctor.(cstr_args)) bbody.

Definition build_map (env : global_env) (st : state) (ind : inductive) (ind_body : one_inductive_body) : TM term := 
  (* Create some universes for the types of A and B. *)
  mlet uA <- tmQuoteUniverse ;;
  mlet uB <- tmQuoteUniverse ;;
  (* Create the type of the mapping function. *)
  (*mlet map_ty <-
    (kp_tProd {| binder_name := nNamed "A" ; binder_relevance := Relevant |} (tSort $ sType uA) None st $ fun A st =>
    kp_tProd {| binder_name := nNamed "B" ; binder_relevance := Relevant |} (tSort $ sType uB) None st $ fun B st =>
    ret (mk_arrow 
      (mk_arrow (tRel $ get_rel A st) (tRel $ get_rel B st))
      (mk_arrow (tApp (tInd ind []) [tRel $ get_rel A st]) (tApp (tInd ind []) [tRel $ get_rel B st]))))
  ;;*)
  (* Abstract over the input parameters. *)
  kp_tLambdaM {| binder_name := nNamed "A" ; binder_relevance := Relevant |} (tSort $ sType uA) st $ fun A st => 
  kp_tLambdaM {| binder_name := nNamed "B" ; binder_relevance := Relevant |} (tSort $ sType uB) st $ fun B st =>
  kp_tLambdaM {| binder_name := nNamed "f" ; binder_relevance := Relevant |} (mk_arrow (tRel $ get_rel A st) (tRel $ get_rel B st)) st $ fun f st =>
  kp_tLambdaM {| binder_name := nNamed "x" ; binder_relevance := Relevant |} (tApp (tInd ind []) [tRel $ get_rel A st]) st $ fun x st =>
  (* Gather the parameters. *)
  let p := {| ind := ind ; map := "map#dummy" ; A := A ; B := B ; f := f ; x := x |} in
  (* Construct the case information. *)
  let ci := {| ci_ind := ind ; ci_npar := 1 ; ci_relevance := Relevant |} in
  (* Construct the case predicate. *)
  let pred := 
    {| puinst := []
    ;  pparams := [tRel $ get_rel A st]
    ;  pcontext := [{| binder_name := nNamed "x" ; binder_relevance := Relevant |}]
    ;  preturn := tApp (tInd ind []) [lift0 1 $ tRel (get_rel B st)] |}
  in
  (* Construct the branches. *)
  mlet branches <- monad_mapi (build_branch env st p) ind_body.(ind_ctors) ;;
  (* Finally make the case expression. *)
  tmReturn (tCase ci pred (tRel $ get_rel x st) branches).

(* [env_of_term ts] returns the global environment needed to type the terms in [ts]. 

   This function is maybe slower than it should be (I use [merge_global_envs] a lot).
   If performance becomes an issue you can try calling [tmQuoteRec] only once,
   on the list of unquoted terms. I tried this approach but failed to deal
   with the dependent typing and universe issues it caused (all the terms in [ts] might
   have different types).
*)
Fixpoint env_of_terms (ts : list term) : TM global_env :=
  match ts with 
  | [] => tmReturn empty_global_env
  | t :: ts =>
    (* Get the environment for [t]. *)
    mlet t <- tmUnquote t ;;
    mlet (t_env, _) <- tmQuoteRec (my_projT2 t) ;;
    (* Get the environment for [ts]. *)
    mlet ts_env <- env_of_terms ts ;;
    (* Merge both envs. *)
    tmReturn (merge_global_envs t_env ts_env)
  end.

(** DeriveMap command entry point. *)
Definition derive_map (ind_name : qualid) : TM unit := 
  (* Locate the inductive. *)
  mlet ind_ref <- tmLocate1 ind_name ;; 
  mlet ind <- 
    match ind_ref with 
    | IndRef ind => tmReturn ind
    | _ => tmFail "Provided constant is not an inductive." 
    end ;;
  (* Get the environment needed to build the mapping function.
     Take care to include the environment needed to type :
     - the given inductive [ind].
     - all the mapping functions in the database. *)
  mlet env <- env_of_terms (tInd ind [] :: [] (*:: List.map (fun name => tConst name []) name_db*)) ;;
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
  mlet func <- build_map env init_state ind ind_body ;;
  tmPrint "The resulting function :" ;;
  (* Add the mapping function to the global environment. *)
  (* TODO : handle the case where [ind_name] contains dots '.' *)
  tmMkDefinition (ind_name ++ "_map")%bs func ;;
  tmReturn tt.