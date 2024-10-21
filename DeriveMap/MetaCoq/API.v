(** Copied from Thomas Lamiaux's "generating recursors" project :
    https://github.com/thomas-lamiaux/generating_recursors 
*)

From Coq Require Export List.
Export ListNotations.

From MetaCoq.Utils Require Export utils.
From MetaCoq.Template Require Export All.

Set Universe Polymorphism.

(* Aux Functions *)
Definition isSome {A} : option A -> bool :=
  fun x => match x with Some _ => true | _ => false end.


Definition fold_right_i {A B} : (nat -> B -> A -> A) -> A -> list B -> A :=
  fun f a =>
  let fix aux n l : A :=
    match l with
    | [] => a
    | b :: l => f n b (aux (S n) l)
  end in
  aux 0.

Definition fold_left_i {A B} : (nat -> A -> B -> A) -> list B -> A -> A :=
  fun f =>
  let fix aux n l a0 : A :=
    match l with
    | [] => a0
    | b :: l => aux (S n) l (f n a0 b)
  end in
  aux 0.

Definition find_errori {A} (p : A -> bool) (l : list A) (default : A) : nat * A :=
  let fix aux n l : nat * A :=
    match l with
    | [] => (n , default)
    | a::l => if p a then (n, a) else aux (S n) l
    end
  in aux 0 l.

(*

This interface is inspired from work by Weituo DAI, and Yannick Forester

#############################
###      Constrains       ###
#############################

1. Be able to refer to variables indirectly by names
2. Keep track of the old variables for weakening
3. Be able to replace variables by term on the fly


#############################
###   Backend interface   ###
#############################


(* 0. Datastructre and General Purposed Functions *)
- state_decl : Type
- state : Type
- init_state : state


(* 1. General Purposed Functions *)
- fold_right_state : {A B X Y Z} : (nat -> A -> state -> (X -> Y -> Z -> state -> B) -> B)
  -> list A -> state -> (list X -> list Y -> list Z -> state -> B) -> B fold_right_state2, fold_right_state3
- fold_left_state : {A B X Y Z} : (nat -> A -> state -> (X -> Y -> Z -> state -> B) -> B)
  -> list A -> state -> (list X -> list Y -> list Z -> state -> B) -> B fold_right_state2, fold_right_state3
- fold_right_state_opt {A B X} : (tp : nat -> A -> state -> (list X -> state -> B) -> B)
  -> list A -> state -> (list X -> state -> B) : B
- fold_left_state_opt {A B X} : (tp : nat -> A -> state -> (list X -> state -> B) -> B)
  -> list A -> state -> (list X -> state -> B) : B

=> 2 and 3 variants

- add_idecl : state_decl -> state -> state
- add_pdecl : state_pdecl -> state -> state
- fresh_ident : option ident -> state -> ident
- fresh_id_context : option ident -> state -> context -> list ident * list (ident * context_decl)
- get_id1: list ident -> nat -> ident
- get_id2 : list (list ident) -> nat -> nat -> ident


(* 2. Debug and Printing Functions *)
- state_to_term : state -> list term


(* 3. Access the inductive type *)
- get_pdecl : kername -> state -> state_pdecl
- get_uparams     : kername -> state -> context
- get_nb_uparams  : kername -> state -> nat
- get_nuparams    : kername -> state -> context
- get_nb_nuparams : kername -> state -> nat
- get_params      : kername -> state -> context
- get_nb_params   : kername -> state -> nat
- get_mdecl       : kername -> state -> mutual_inductive_body
- get_ind_bodies  : kername -> state -> list one_inductive_body
- get_indb        : kername -> nat  -> state -> one_inductive_body
- get_relevance   : kername -> nat  -> state -> relevance
- get_ctor        : kername -> nat  -> nat  -> state -> constructor_body


(* 4. Access the context *)
- get_one_term     : ident -> state -> term
- get_one_of_term  : list ident -> nat -> state -> term
- get_one_of_term2 : list (list ident) -> nat -> nat -> state -> term
- get_term         : list ident -> state -> list term
- get_one_type     : ident -> state -> term
- get_type         : list ident -> state -> list term
- get_typing_context : state -> context
- get_aname : list ident -> state -> list aname :=
  (checks var value / body depending status)
- check_term : state -> ident -> term -> bool


(* 5. Weakening and Lets *)
- weaken : state -> term -> term
- weaken_decl : state -> context_decl -> context_decl

(* 6. Add Inductive Types *)
add_mdecl : kername -> nat -> mutual_inductive_body -> state -> state  :=


(* 7. Add variables *)
- init_state : state
- add_old_var : ident -> context_decl -> state -> state
- add_old_context : list (ident * context_decl) -> state -> state
- add_fresh_var : ident -> context_decl -> state -> state
- add_fresh_context : list (ident * context_decl) -> state -> state
- add_replace_var : ident -> context_decl -> term -> state -> state
- add_unscoped_var : ident -> context_decl -> term -> state -> state
- add_replace_context : list (ident * context_decl) -> list term -> state -> state
- weaken_context : state -> context -> context


(* 8. Notations *)
- weaken "s ↑"
- bind "let* x .. z '<-' c1 'in' c2"

*)




(* 0. Datastructre and General Purposed Functions *)
Record state_decl : Type := mk_idecl
  { state_name    : ident ;
    state_old     : bool ;
    state_replace : bool ;
    state_scope   : bool ;
    state_def     : context_decl ;
}.

Record state_pdecl : Type := mk_pdecl
{ state_kname       : kername ;
  state_uparams     : context ;
  state_nb_uparams  : nat ;
  state_nuparams    : context ;
  state_nb_nuparams : nat ;
  state_mdecl       : mutual_inductive_body ;
}.

Record state : Type := mk_state
{ state_context : list state_decl;
  state_ind : list state_pdecl ;
}.


Definition init_state : state := mk_state [] [].

Axiom failwith : forall A, string -> A.
Arguments failwith {_} _.

(* 1. General Purposed Functions  *)

(* 1.1 Fold_left and Fold_right *)
Definition fold_right_state {A B X} (tp : nat -> A -> state -> (X -> state -> B) -> B)
  (l:list A) (s:state) (t : list X -> state -> B) : B :=
  let fix aux n ids1 l s t : B :=
    match l with
    | [] => t (rev ids1) s
    | a :: l => tp n a s (fun id1 s => aux (S n) (id1 :: ids1) l s t)
  end in
  aux 0 [] l s t.

  Definition fold_right_state2 {A B X Y} (tp : nat -> A -> state -> (X -> Y -> state -> B) -> B)
  (l:list A) (s:state) (t : list X -> list Y -> state -> B) : B :=
  let fix aux n ids1 ids2 l s t : B :=
    match l with
    | [] => t (rev ids1) (rev ids2) s
    | a :: l => tp n a s (fun id1 id2 s => aux (S n) (id1 :: ids1) (id2 :: ids2) l s t)
  end in
  aux 0 [] [] l s t.

Definition fold_right_state3 {A B X Y Z} (tp : nat -> A -> state -> (X -> Y -> Z -> state -> B) -> B)
  (l:list A) (s:state) (t : list X -> list Y -> list Z -> state -> B) : B :=
  let fix aux n ids1 ids2 ids3 l s t : B :=
    match l with
    | [] => t (rev ids1) (rev ids2) (rev ids3) s
    | a :: l => tp n a s (fun id1 id2 id3 s => aux (S n) (id1 :: ids1) (id2 :: ids2) (id3 :: ids3) l s t)
  end in
  aux 0 [] [] [] l s t.

Definition fold_left_state {A B X} (tp : nat -> A -> state -> (X -> state -> B) -> B)
  (l:list A) (s:state) (t : list X -> state -> B) : B :=
  fold_right_state tp (rev l) s t.

Definition fold_left_state2 {A B X Y} (tp : nat -> A -> state -> (X -> Y -> state -> B) -> B)
  (l:list A) (s:state) (t : list X -> list Y -> state -> B) : B :=
  fold_right_state2 tp (rev l) s t.

Definition fold_left_state3 {A B X Y Z} (tp : nat -> A -> state -> (X -> Y -> Z -> state -> B) -> B)
  (l:list A) (s:state) (t : list X -> list Y -> list Z -> state -> B) : B :=
  fold_right_state3 tp (rev l) s t.

(* 1.2 Fold_right and Fold_left conditional *)
Definition fold_right_state_opt {A B X} (tp : nat -> A -> state -> (list X -> state -> B) -> B)
  (l:list A) (s:state) (t : list X -> state -> B) : B :=
  let fix aux n ids1 l s t : B :=
    match l with
    | [] => t (rev ids1) s
    | a :: l => tp n a s (fun fid1 s => aux (S n) (fid1 ++ ids1) l s t)
  end in
  aux 0 [] l s t.

Definition fold_right_state_opt2 {A B X Y} (tp : nat -> A -> state -> (list X -> list Y -> state -> B) -> B)
  (l:list A) (s:state) (t : list X -> list Y -> state -> B) : B :=
  let fix aux n ids1 ids2 l s t : B :=
    match l with
    | [] => t (rev ids1) (rev ids2) s
    | a :: l => tp n a s (fun fid1 fid2 s => aux (S n) (fid1 ++ ids1) (fid2 ++ ids2) l s t)
  end in
  aux 0 [] [] l s t.

Definition fold_right_state_opt3 {A B X Y Z} (tp : nat -> A -> state -> (list X -> list Y -> list Z -> state -> B) -> B)
  (l:list A) (s:state) (t : list X -> list Y -> list Z -> state -> B) : B :=
  let fix aux n ids1 ids2 ids3 l s t : B :=
    match l with
    | [] => t (rev ids1) (rev ids2) (rev ids3) s
    | a :: l => tp n a s (fun fid1 fid2 fid3 s => aux (S n) (fid1 ++ ids1) (fid2 ++ ids2) (fid3 ++ ids3) l s t)
  end in
  aux 0 [] [] [] l s t.

Definition fold_left_state_opt {A B X} (tp : nat -> A -> state -> (list X -> state -> B) -> B)
  (l:list A) (s:state) (t : list X -> state -> B) : B :=
  fold_right_state_opt tp (rev l) s t.

Definition fold_left_state_opt2 {A B X Y} (tp : nat -> A -> state -> (list X -> list Y -> state -> B) -> B)
  (l:list A) (s:state) (t : list X -> list Y -> state -> B) : B :=
  fold_right_state_opt2 tp (rev l) s t.

Definition fold_left_state_opt3 {A B X Y Z} (tp : nat -> A -> state -> (list X -> list Y -> list Z -> state -> B) -> B)
  (l:list A) (s:state) (t : list X -> list Y -> list Z -> state -> B) : B :=
  fold_right_state_opt3 tp (rev l) s t.

(* 1.3 Others *)
Definition add_idecl : state_decl -> state -> state :=
  fun idecl s => mk_state (idecl :: s.(state_context)) s.(state_ind).

Definition add_pdecl : state_pdecl -> state -> state :=
  fun pdecl s => mk_state s.(state_context) (pdecl :: s.(state_ind)).

Definition check_ident : ident -> state_decl -> bool :=
  fun i idecl => eqb idecl.(state_name) i.

Definition fresh_ident_aux : option ident -> nat -> ident :=
  fun x k => match x with
  | Some s => String.append s (string_of_nat k)
  | None   => String.append "Var" (string_of_nat k)
  end.

Definition fresh_ident : option ident -> state -> ident :=
  fun x s => fresh_ident_aux x (length s.(state_context)).

Definition fresh_id_context : option ident -> state -> context -> list ident * list (ident * context_decl) :=
  fun x s cxt =>
    let le := length s.(state_context) in
    let id_cxt := (mapi (fun i cdecl => (fresh_ident_aux x (i + le), cdecl)) (rev cxt)) in
    (map fst id_cxt, rev id_cxt).

Definition get_id1: list ident -> nat -> ident :=
  fun ids pos_id => nth pos_id ids (failwith "error get one of them").

Definition get_id2 : list (list ident) -> nat -> nat -> ident :=
  fun idss pos1 pos2 =>
  let ids := nth pos1 idss (failwith "error get2 pos1") in
  nth pos2 ids (failwith "error get2 pos2").



(* 2. Debug and Printing Functions *)
Notation "x ^^ y" := (x ^ " ; " ^ y ) (left associativity, at level 50).

Definition show_def : string -> string -> string :=
  fun key value => key ^ " := " ^ value.

Definition show_kername : kername -> string :=
  fun kname => show_def "kername" (snd kname).

Definition show_state_decl : state_decl -> string :=
  fun ' (mk_idecl name old replace scope (mkdecl an db ty)) =>
     show_def "state_name"      (name)
  ^^ show_def "state_old"       (string_of_bool old)
  ^^ show_def "state_replace"   (string_of_bool replace)
  ^^ show_def "state_scope"     (string_of_bool scope)
  ^^ show_def "state_decl_type" (string_of_term ty)
  ^^ show_def "state_decl_body" (string_of_option (string_of_term) db).

Definition show_state : state -> string :=
  fun s => fold_left String.append (map show_state_decl s.(state_context)) "".

Definition state_to_term : state -> list term :=
  fun s => map (fun idecl => tVar (show_state_decl idecl)) (rev s.(state_context)).

Definition show_error_kname : kername -> state -> string :=
  fun kname s =>
      show_kername kname
  ^^ show_state s.

Definition show_error_indb : kername -> nat -> state -> string :=
  fun kname pos_indb s =>
      show_kername kname
  ^^ show_def "pos_indb" (string_of_nat pos_indb)
  ^^ show_state s.

Definition show_error_ctor : kername -> nat -> nat -> state -> string :=
  fun kname pos_indb pos_ctor s =>
      show_kername kname
  ^^ show_def "pos_indb" (string_of_nat pos_indb)
  ^^ show_def "pos_ctor" (string_of_nat pos_ctor)
  ^^ show_state s.



(* 3. Access the inductive types *)
Definition get_pdecl : kername -> state -> state_pdecl :=
  fun kname s =>
    match find (fun pdecl => eqb pdecl.(state_kname) kname) s.(state_ind) with
    | Some pdecl => pdecl
    | None => failwith ("get_pdecl => " ^ show_error_kname kname s)
    end.

Definition get_uparams : kername -> state -> context :=
  fun kname s => (get_pdecl kname s).(state_uparams).

Definition get_nb_uparams : kername -> state -> nat :=
  fun kname s => (get_pdecl kname s).(state_nb_uparams).

Definition get_nuparams : kername -> state -> context :=
  fun kname s => (get_pdecl kname s).(state_nuparams).

Definition get_nb_nuparams : kername -> state -> nat :=
  fun kname s => (get_pdecl kname s).(state_nb_nuparams).

Definition get_params : kername -> state -> context :=
  fun kname s => (get_pdecl kname s).(state_mdecl).(ind_params).

Definition get_nb_params : kername -> state -> nat :=
  fun kname s => (get_pdecl kname s).(state_mdecl).(ind_npars).

Definition get_mdecl : kername -> state -> mutual_inductive_body :=
  fun kname s => (get_pdecl kname s).(state_mdecl).

Definition get_ind_bodies : kername -> state -> list one_inductive_body :=
  fun kname s => (get_pdecl kname s).(state_mdecl).(ind_bodies).

Definition get_indb : kername -> nat -> state -> one_inductive_body :=
  fun kname pos_indb s => nth pos_indb (get_ind_bodies kname s)
    (failwith (show_error_indb kname pos_indb s)).

Definition get_relevance : kername -> nat -> state -> relevance :=
  fun kname pos_indb s => (get_indb kname pos_indb s).(ind_relevance).

Definition get_ctor : kername -> nat -> nat -> state -> constructor_body :=
  fun kname pos_indb pos_ctor s => nth pos_ctor (get_indb kname pos_indb s).(ind_ctors)
    (failwith (show_error_ctor kname pos_indb pos_ctor s)).



(* 4. Acces the Context *)

(* Aux *)
Definition get_term_idecl : nat -> state_decl -> term :=
  fun pos_idecl idecl =>
  match idecl.(state_def).(decl_body) with
  | Some tm => if idecl.(state_replace)
                then (if idecl.(state_scope) then lift0 (S pos_idecl) tm  else lift0 pos_idecl tm)
               else tRel pos_idecl
  | None => tRel pos_idecl
  end.

Definition get_type_idecl : nat -> state_decl -> term :=
  fun pos_idecl idecl => lift0 (S pos_idecl) idecl.(state_def).(decl_type).

Definition get_state : (nat -> state_decl -> term) -> (state_decl -> bool) ->  state -> list term :=
  fun f p s =>
  let fix aux i s :=
  match s with
  | [] => []
  | idecl :: s =>
    let next := (if idecl.(state_scope) then aux (S i) s else aux i s) in
    if p idecl then f i idecl :: next else next
  end in
  aux 0 s.(state_context).

Definition get_term_state : (state_decl -> bool) -> state -> list term :=
  get_state get_term_idecl.

Definition get_type_state : (state_decl -> bool) -> state -> list term :=
  get_state get_type_idecl.

Definition get_idecl : ident -> state -> (nat * state_decl) :=
  fun id s =>
  let fix aux n s' :=
  match s' with
  | [] => failwith ("get_idecl => " ^ id ^ " NOT IN SCOPE " ^ show_state s)
  | idecl :: s' => if eqb id idecl.(state_name) then (n, idecl)
                    else if idecl.(state_scope) then aux (S n) s' else aux n s'
  end in
  aux 0 s.(state_context).

(* 1.3 Get terms and type *)
Definition get_one_term : ident -> state -> term :=
  fun id s => let ' (pos_var, idecl) := get_idecl id s in
              get_term_idecl pos_var idecl.

Definition get_one_of_term : list ident -> nat -> state -> term :=
  fun ids pos_id s =>
    let ' (pos_var, idecl) := get_idecl (get_id1 ids pos_id) s in
    get_term_idecl pos_var idecl.

Definition get_one_of_term2 : list (list ident) -> nat -> nat -> state -> term :=
  fun idss pos1 pos2 s =>
    let ' (pos_var, idecl) := get_idecl (get_id2 idss pos1 pos2) s in
    get_term_idecl pos_var idecl.

Definition get_term : list ident -> state -> list term :=
  fun ids s => map (fun id => get_one_term id s) ids.

Definition get_one_type : ident -> state -> term :=
fun id s => let ' (pos_var, idecl) := get_idecl id s in
            get_type_idecl pos_var idecl.

Definition get_type : list ident -> state -> list term :=
fun ids s => map (fun id => get_one_type id s) ids.

  (* Works ??? *)
Definition get_typing_context : state -> context :=
  fun s => map state_def s.(state_context).

Definition get_one_aname : ident -> state -> aname :=
  fun id s => let ' (_, idecl) := get_idecl id s in
              idecl.(state_def).(decl_name).

Definition get_aname : list ident -> state -> list aname :=
  fun ids s => map (fun id => get_one_aname id s) ids.

Definition check_term : state -> ident -> term -> bool :=
  fun s id tm => eqb (get_one_term id s) tm.



(* 5. Weakening and Lets *)
Definition get_subst : state -> list term :=
  get_term_state state_old.

Definition weaken : state -> term -> term :=
  fun s => subst0 (get_subst s).

Definition weaken_decl : state -> context_decl -> context_decl :=
  fun s cdecl =>
  let ' (mkdecl an db ty) := cdecl in
  mkdecl an (option_map (weaken s) db) (weaken s ty).



(* 6. Add Inductive Types *)
Definition add_mdecl : kername -> nat -> mutual_inductive_body -> state -> state  :=
  fun kname nb_uparams mdecl s =>
    let rev_params := rev mdecl.(ind_params) in
    add_pdecl (
      mk_pdecl kname
               (rev (firstn nb_uparams rev_params)) nb_uparams
               (rev (skipn nb_uparams rev_params)) (mdecl.(ind_npars) - nb_uparams)
               mdecl) s.


(* 7. Add variables *)
Definition add_old_var : ident -> context_decl -> state -> state :=
  fun x decl s => add_idecl (mk_idecl x true false true (weaken_decl s decl)) s.

Definition add_old_context : list (ident * context_decl) -> state -> state :=
  fun id_cxt s => fold_right (fun ' (id, cdecl) s => add_old_var id cdecl s) s id_cxt.

Definition add_fresh_var : ident -> context_decl -> state -> state :=
  fun x decl s => add_idecl (mk_idecl x false false true decl) s.

Definition add_fresh_context : list (ident * context_decl) -> state -> state :=
  fun id_cxt s => fold_right (fun ' (id, cdecl) s => add_fresh_var id cdecl s) s id_cxt.

Definition add_replace_var : ident -> context_decl -> term -> state -> state :=
  fun x cxt tm s => let ' mkdecl an _ ty := weaken_decl s cxt in
                    add_idecl (mk_idecl x true true true (mkdecl an (Some tm) ty)) s.

Definition add_unscoped_var : ident -> context_decl -> term -> state -> state :=
  fun x cxt tm s => let ' mkdecl an _ ty := weaken_decl s cxt in
                    add_idecl (mk_idecl x false true false (mkdecl an (Some tm) ty)) s.

(* Warning needs list of same length *)
(* terms are in reversed order *)
Definition add_replace_context : list (ident * context_decl) -> list term -> state -> state :=
  fun id_cxt ltm s =>
  fold_right (fun ' ((id, cdecl), tm) s => add_replace_var id cdecl tm s)
  s (combine id_cxt (rev ltm)).

Definition weaken_context : state -> context -> context :=
  fun s cxt =>
  fold_right_state (
    fun i cdecl s t =>
    let cdecl' := weaken_decl s cdecl in
    let s' := add_old_var "foo" cdecl s in
    cdecl' :: (t I s'))
  cxt s (fun _ _ => []).



(* 8. Notations *)
Notation "s ↑" := (weaken s) (at level 10).

Notation "let* x .. z '<-' c1 'in' c2" := (c1 (fun x => .. (fun z => c2) ..))
(at level 100, x binder, z binder, c1 at next level, right associativity).




(* ########################################################################## *)
(* ########################################################################## *)
(* ########################################################################## *)

(*
#############################
###  Frontend interface   ###
#############################



(* 1. Inductive Types *)
replace_ind : kername -> state -> (list ident) * state
make_ind : kername -> nat -> list ident -> list ident -> list ident -> state -> term
make_cst : kername -> nat -> nat -> list ident -> list ident -> state -> term
get_indices : kername -> nat -> state -> context
get_ctor_indices : kername -> nat -> nat -> state -> list term



(* 2. Keep and Add Binders *)
kp_tLetIn : aname -> term -> term -> state -> (ident -> state -> term) -> term
mk_tLetIn : aname -> term -> term -> state -> (ident -> state -> term) -> term

Context (aname -> term -> term -> term).

  (* Keep Binder *)
  kp_binder : aname -> term -> option ident -> state -> (ident -> state -> term) -> term
  it_kp_binder : (aname -> term -> term -> term) -> context -> option ident -> state -> (list ident -> state -> term) -> term
  closure_uparams : (aname -> term -> term -> term) -> kername -> state -> (list ident -> state -> term) -> term
  closure_nuparams : (aname -> term -> term -> term) -> kername -> state -> (list ident -> state -> term) -> term
  closure_params : (aname -> term -> term -> term) -> kername -> state -> (list ident -> state -> term) -> term

  (* Make Binders *)
  mk_binder : aname -> term -> option ident -> state -> (ident -> state -> term) -> term
  closure_binder {A} (x : option ident) (l : list A)
  closure_indices : kername -> nat -> state -> (list ident -> state -> term) -> term

  End.

mk_tProd : aname -> term -> option ident -> state -> (ident -> state -> term) -> term
mk_tLambda : aname -> term -> option ident -> state -> (ident -> state -> term) -> term

kp_tProd := aname -> term -> option ident -> state -> (ident -> state -> term) -> term
kp_tLambda := aname -> term -> option ident -> state -> (ident -> state -> term) -> term


mk_tFix : ... -> nat -> state -> (list ident -> nat -> one_inductive_body -> state -> term) -> term
mk_tCase : ... -> term -> state -> (nat -> constructor_body -> state -> branch term) -> term :=



(* 3. Reduction *)
- reduce_except_lets : state -> term -> term
- reduce_full : state -> term -> term


(* 4. Decide Interface *)
- check_args_by_arg : (term -> state -> A) -> context -> state -> A
- check_ctors_by_arg : (term -> state -> A) -> list context -> state -> A
- debug_check_args_by_arg {A} : global_env -> (term -> state -> A) -> context -> state -> list A
- debug_check_ctors_by_arg {A} : global_env -> (term -> state -> A) -> list context -> state -> list (list A)
- get_args : mutual_inductive_body -> list context
*)



(* 1. Inductive Types *)
Definition ind_to_cxt : kername -> state -> context :=
  fun kname s =>
  map (fun indb => mkdecl (mkBindAnn nAnon indb.(ind_relevance)) None indb.(ind_type))
  (rev (get_ind_bodies kname s)).

Definition ind_to_terms : kername -> state -> list term :=
  fun kname s => mapi (fun i _ => (tInd (mkInd kname i) [])) (get_ind_bodies kname s).

Definition replace_ind : kername -> state -> (list ident) * state :=
  fun kname s =>
  let ' (id_inds, id_cxt_inds) := fresh_id_context (Some "Ind") s (ind_to_cxt kname s) in
  let s := add_replace_context id_cxt_inds (ind_to_terms kname s) s in
  (id_inds, s).

(* Builds: Ind A1 ... An B0 ... Bm i1 ... il *)
Definition make_ind : kername -> nat -> list ident -> list ident -> list ident -> state -> term :=
  fun kname pos_indb id_uparams id_nuparams id_indices s =>
  mkApps (tInd (mkInd kname pos_indb) [])
          (  get_term id_uparams  s
          ++ get_term id_nuparams s
          ++ get_term id_indices s).

(* Builds: Cst A1 ... An B0 ... Bm *)
Definition make_cst : kername -> nat -> nat -> list ident -> list ident -> state -> term :=
  fun kname pos_indb pos_ctor id_uparams id_nuparams s =>
  mkApps (tConstruct (mkInd kname pos_indb) pos_ctor [])
          (get_term id_uparams s ++ get_term id_nuparams s).

Arguments make_cst _ pos_indb pos_ctor id_uparams id_nuparams _.

Definition get_indices : kername -> nat -> state -> context :=
  fun kname pos_indb s => weaken_context s (get_indb kname pos_indb s).(ind_indices).

Definition get_ctor_indices : kername -> nat -> nat -> state -> list term :=
  fun kname pos_indb pos_ctor s => map (s ↑) (get_ctor kname pos_indb pos_ctor s).(cstr_indices).



(* 2. Keep and Add Binders *)
Definition kp_tLetIn : aname -> term -> term -> state -> (ident -> state -> term) -> term :=
  fun an db t1 s t2 =>
    let id := fresh_ident (Some "LET") s in
    let db' := s ↑ db in
    let t1' := s ↑ t1 in
    let s := add_old_var id (mkdecl an (Some db) t1) s in
    tLetIn an db' t1' (t2 id s).

Definition mk_tLetIn : aname -> term -> term -> state -> (ident -> state -> term) -> term :=
  fun an db t1 s t2 =>
    let id := fresh_ident (Some "LET") s in
    let s := add_fresh_var id (mkdecl an (Some db) t1) s in
    tLetIn an db t1 (t2 id s).

Section Binder.

  Context (binder : aname -> term -> term -> term).

  Definition kp_binder : aname -> term -> option ident -> state -> (ident -> state -> term) -> term :=
    fun an t1 x s t2 =>
      let id := fresh_ident x s in
      let t1' := s ↑ t1 in
      let s  := add_old_var id (mkdecl an None t1) s in
      binder an t1' (t2 id s).

  (** Monadic variant of [kp_binder]. *)
  Definition kp_binderM {M} `{Monad M} (an : aname) (ty : term) (st : state) (k : ident -> state -> M term) : M term :=
    let id := fresh_ident None st in
    let ty' := st ↑ ty in
    let st := add_old_var id (mkdecl an None ty) st in
    bind (k id st) (fun body => ret (binder an ty' body)).

  Definition it_kp_binder : context -> option ident -> state -> (list ident -> state -> term) -> term :=
    fun cxt x => fold_left_state
    (fun _ cdecl s t =>
      let '(mkdecl an db ty) := cdecl in
      match db with
      | None => kp_binder an ty x s t
      | Some db => kp_tLetIn an db ty s t
      end) cxt.

  (* new functions *)
  Definition closure_uparams : kername -> state -> (list ident -> state -> term) -> term :=
    fun kname s => it_kp_binder (get_uparams kname s) (Some "uparams") s.

  Definition closure_nuparams : kername -> state -> (list ident -> state -> term) -> term :=
    fun kname s => it_kp_binder (get_nuparams kname s) (Some "nuparams") s.

  Definition closure_params : kername -> state -> (list ident -> state -> term) -> term :=
  fun kname s => it_kp_binder (get_params kname s) (Some "params") s.


  Definition mk_binder : aname -> term -> option ident -> state -> (ident -> state -> term) -> term :=
    fun an t1 x s t2 =>
      let id := fresh_ident x s in
      let s := add_fresh_var id (mkdecl an None t1) s in
      binder an t1 (t2 id s).

  Definition it_mk_binder : context -> option ident -> state -> (list ident -> state -> term) -> term :=
    fun cxt x => fold_left_state
    (fun _ cdecl s t =>
      let '(mkdecl an db ty) := cdecl in
      match db with
      | None => mk_binder an ty x s t
      | Some db => mk_tLetIn an db ty s t
      end) cxt.

  Definition closure_binder {A} (x : option ident) (l : list A)
    (naming : nat -> A -> aname) (typing : nat -> A -> state -> term) :
    state -> (list ident -> state -> term) -> term :=
    fold_right_state
      (fun n a s t => mk_binder (naming n a) (typing n a s) x s t)
      l .

  Definition closure_indices : kername -> nat -> state -> (list ident -> state -> term) -> term :=
    fun kname pos_indb s => it_mk_binder (get_indices kname pos_indb s) (Some "indices") s.

End Binder.

Definition kp_tProd := kp_binder tProd.
Definition kp_tLambda := kp_binder tLambda.

Definition kp_tProdM := kp_binderM tProd.
Definition kp_tLambdaM := kp_binderM tLambda.

Definition mk_tProd := mk_binder tProd.
Definition mk_tLambda := mk_binder tLambda.



Section mk_tFix.
  Context (ind_bodies : list one_inductive_body).
  Context (fan   : nat -> one_inductive_body -> state -> aname).
  Context (fty   : nat -> one_inductive_body -> state -> term).
  Context (frarg : nat -> one_inductive_body -> state -> nat).

  Definition mk_tFix : nat -> state -> (list ident -> nat -> one_inductive_body -> state -> term) -> term :=
    fun focus s tmc =>
    let cxt_fix := rev (mapi (fun pos_indb indb => mkdecl (fan pos_indb indb s) None (fty pos_indb indb s)) ind_bodies) in
    let ' (id_fix, id_cxt_fix) := fresh_id_context (Some "Fix") s cxt_fix in
    let e_Fix := add_fresh_context id_cxt_fix s in
    tFix (mapi (fun pos_indb indb => mkdef _ (fan pos_indb indb s) (fty pos_indb indb s)
                    (tmc id_fix pos_indb indb e_Fix) (frarg pos_indb indb s)) ind_bodies) focus.

End mk_tFix.


  Section MktCase.
  Context (kname : kername).
  Context (pos_indb : nat).
  Context (indb : one_inductive_body).

  Context (mk_case_info : nat -> one_inductive_body -> state -> case_info).
  Context (mk_case_pred : list ident -> ident -> nat -> one_inductive_body -> state -> term).
  Context (id_uparams id_nuparams : list ident).

  Definition mk_state_pred : state -> list ident * ident * state :=
    fun s =>
    let ' (id_findices , id_cxt_indices) := fresh_id_context None s indb.(ind_indices) in
    let e_pred := add_fresh_context id_cxt_indices s in
    let fVarMatch := (mkdecl (mkBindAnn nAnon indb.(ind_relevance)) None
                          (make_ind kname pos_indb id_uparams id_nuparams id_findices e_pred)) in
    let id_fVarMatch := fresh_ident None e_pred in
    let e_pred := add_fresh_var id_fVarMatch fVarMatch e_pred in
    (id_findices, id_fVarMatch, e_pred).

  Definition mk_pred : state -> predicate term :=
    fun s =>
    let ' (id_findices, id_fVarMatch, e_pred) := mk_state_pred s in
    mk_predicate []
      ((get_term id_uparams s ++ get_term id_nuparams s))
      (get_aname [id_fVarMatch] e_pred ++ get_aname id_findices e_pred)
      (mk_case_pred id_findices id_fVarMatch pos_indb indb e_pred).

  Definition mk_tCase : term -> state -> (nat -> constructor_body -> state -> branch term) -> term :=
    fun tm_match s branch =>
    tCase (mk_case_info pos_indb indb s) (mk_pred s) tm_match
    (mapi (fun pos_ctor ctor => branch pos_ctor ctor s) indb.(ind_ctors)).

End MktCase.



(* 3. Reduction *)
From MetaCoq Require Import Template.Checker.
Import RedFlags.

Definition noiota_flags := mk true true false true true true.

Definition reduce_except_lets :  global_env -> state -> term -> term :=
  fun E s t =>
  match reduce_opt noiota_flags empty_global_env (get_typing_context s) 5000 t with
  | Some t => t
  | None => tVar "ERREUR REDUCTION"
  end.

Definition reduce_lets : state -> term -> term :=
  fun s t => expand_lets (get_typing_context s) t.

Definition reduce_full : global_env -> state -> term -> term :=
  fun E s t =>
  match reduce_opt default E (get_typing_context s) 5000 t with
  | Some t => t
  | None => tVar "ERREUR REDUCTION"
  end.



(* ########################################################################## *)
(* ########################################################################## *)
(* ########################################################################## *)

(*
#############################
###    Decide interface   ###
#############################

*)

Section CheckArg.

  Context {A : Type}.
  Context (bop : A -> A -> A).
  Context (default : A).
  Context (E : global_env).
  Context (kname : kername).

Definition check_args_by_arg : (term -> state -> A) -> context -> state -> A :=
  fun check_arg args s =>
  fold_left_state
    ( fun i arg s t =>
        let rty := reduce_full E s (s ↑ arg.(decl_type)) in
        let id_arg := fresh_ident (Some "arg") s in
        let s' := add_old_var id_arg arg s in
        match arg.(decl_body) with
        | None => bop (check_arg rty s) (t id_arg s')
        | Some _ => t id_arg s'
        end
  )
  args s (fun _ _ => default).

Definition check_ctors_by_arg : (term -> state -> A) -> list context -> state -> A :=
  fun check_arg lcxt s =>
  fold_left bop (map (fun cxt => check_args_by_arg check_arg cxt s) lcxt) default.

End CheckArg.

Definition debug_check_args_by_arg {A} : global_env -> (term -> state -> A) -> context -> state -> list A :=
  fun E check_arg cxt s =>
  check_args_by_arg (@app A) [] E (fun x s => [check_arg x s]) cxt s.

Definition debug_check_ctors_by_arg {A} : global_env -> (term -> state -> A) -> list context -> state -> list (list A) :=
  fun E check_arg lcxt s => map (fun cxt => debug_check_args_by_arg E check_arg cxt s) lcxt.

Definition get_args : mutual_inductive_body -> list context :=
  fun mdecl => map cstr_args (concat (map ind_ctors mdecl.(ind_bodies))).