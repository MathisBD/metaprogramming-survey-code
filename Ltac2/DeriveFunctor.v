From Coq Require List.
From Ltac2 Require Import Ltac2 Printf Std.

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

(** Throw a fatal [Tactic_failure] exception with the given message. *)
Ltac2 tactic_fail (msg : string) : 'a :=
  Control.throw (Tactic_failure (Some (Message.of_string msg))).

(** Smart constructor for [Constr.Unsafe.Rel]. *)
Ltac2 mk_rel (n : int) : constr :=
  Constr.Unsafe.make (Constr.Unsafe.Rel n).

(** Smart constructor for [Constr.Unsafe.Var]. *)
Ltac2 mk_var (i : ident) : constr :=
  Constr.Unsafe.make (Constr.Unsafe.Var i).

(** Smart constructor for [Constr.Unsafe.Lambda]. 
    Does not perform term lifting. *)
Ltac2 mk_lambda (bind : binder) (body : constr) : constr := 
  Constr.Unsafe.make (Constr.Unsafe.Lambda bind body).

(** Smart constructor for [Constr.Unsafe.Prod]. 
    Does not perform term lifting. *)
Ltac2 mk_prod (bind : binder) (body : constr) : constr := 
  Constr.Unsafe.make (Constr.Unsafe.Prod bind body).

(** Smart constructor for [Constr.Unsafe.Evar]. *)
Ltac2 mk_evar (ev : evar) (args : constr array) : constr :=
  Constr.Unsafe.make (Constr.Unsafe.Evar ev args).

(** [my_intro basename] creates an identifier from [basename] which is 
    fresh in the current goal, introduces a variable using this identifier 
    and returns it. *)
Ltac2 my_intro (basename : string) : ident :=
  let x := Fresh.in_goal (Option.get (Ident.of_string basename)) in 
  Std.intro (Some x) None ; x.
      
(* [constructor_nargs ctr] returns the number of the arguments of [ctr],
   including parameters. *)
Ltac2 constructor_nargs (ctor : constructor) : int := 
  (* Get the type of the constructor. *)
  let cty := Constr.type (Env.instantiate (Std.ConstructRef ctor)) in
  (* Count the number of arguments. *)
  let rec loop i cty :=
    match Constr.Unsafe.kind cty with 
    | Constr.Unsafe.Prod _ cty => loop (Int.add i 1) cty
    | _ => i
    end
  in 
  loop 0 cty.
      
(* Replace all occurences of [a] with [b] in [t], without performing any lifting. *)
Ltac2 rec replace_subterm (a : constr) (b : constr) (t : constr) : constr := 
  if Constr.equal a t then b else Constr.Unsafe.map (replace_subterm a b) t.

(** [named_lambda x ty body] constructs the lambda abstraction [fun x : ty => body].
    This assumes that [body] does not contain any loose de Bruijn index. *)
Ltac2 named_lambda (x : ident) (ty : constr) (body : constr) : constr :=
  let binder := Constr.Binder.unsafe_make (Some x) Constr.Binder.Relevant ty in
  let body := replace_subterm (mk_var x) (mk_rel 1) body in
  mk_lambda binder body.

(** [fresh_evar ty] creates a new evar which has type [ty]. *)
Ltac2 fresh_evar (ty : constr) : evar :=
  (* Create the evar. *)
  let ev_term := '_ in 
  let ev := 
    match Constr.Unsafe.kind ev_term with  
    | Constr.Unsafe.Evar ev _ => ev 
    | _ => tactic_fail "fresh_evar"
    end
  in 
  (* Set the type of the evar. *)
  Unification.unify_with_current_ts (Constr.type ev_term) ty ;
  ev.

(*************************************************************************************)
(** *** Deriving.  *)
(*************************************************************************************)

Ltac2 build_arg (a : ident) (b : ident) (f : ident) (arg : ident) () : unit :=
  let va := mk_var a in
  let vb := mk_var b in 
  let vf := mk_var f in 
  let varg := mk_var arg in 
  solve 
    [ (* If [A] does not appear in the type of the argument, there is no lifting to be done. *)
      exact $varg 
    | (* Otherwise, lift using [fmap]. *)
      let fctor := named_lambda b (Constr.type (Control.hyp b)) (Control.goal ()) in
      let t := '(@fmap $fctor _ $va $vb $vf $varg) in
      Std.apply false false [fun () => (t, NoBindings)] None ].

Ltac2 build_branch (ind : inductive) (a : ident) (b : ident) (f : ident) (ctor_idx : int) () : unit :=
  (* Count the number of arguments, excluding the (unique) parameter. *)
  let ctor := Ind.get_constructor (Ind.data ind) ctor_idx in
  let n_args := Int.sub (constructor_nargs ctor) 1 in
  (* Introduce the arguments. *)
  let rec loop acc n :=
    if Int.equal n 0 then List.rev acc 
    else 
      let arg := my_intro "arg" in
      loop (arg :: acc) (Int.sub n 1)
  in 
  let args := loop [] n_args in
  (* Apply the constructor corresponding to this branch. *)
  constructor_n false (Int.add 1 ctor_idx) NoBindings ;
  (* Process each argument separately. *)
  Control.dispatch (List.map (build_arg a b f) args).

Ltac2 build_func () : unit :=
  (* Check the goal is of the form [Functor F] and retrieve [F]. *)
  let ind := 
    match! Control.goal () with
    | Functor ?f => 
      match Constr.Unsafe.kind f with 
      | Constr.Unsafe.Ind ind _ => ind 
      | _ => tactic_fail "Goal should be of the form [Functor ?f] where [f] is an inductive type."
      end
    | _ => tactic_fail "Goal should be of the form [Functor ?f]."
    end
  in 
  (* Apply [Build_Functor] and introduce variables. *)
  constructor ;
  let fix_param := Fresh.in_goal @fix_param in 
  fix_ fix_param 4 ;
  let a := my_intro "A" in
  let b := my_intro "B" in 
  let f := my_intro "f" in 
  let x := my_intro "x" in 
  (* Build the recursive instance. *)
  let vfix_param := mk_var fix_param in
  pose (rec_inst := Build_Functor _ $vfix_param) ;
  (* Case analysis and process each branch separately. *)
  Std.case false (Control.hyp x, NoBindings) ;
  Control.dispatch (List.init (Ind.nconstructors (Ind.data ind)) (build_branch ind a b f)).

Ltac2 derive_functor () : unit :=
  (* Copy the current goal. *)
  let ev := fresh_evar (Control.goal ()) in 
  Control.new_goal ev ;
  (* Build the functor instance on the new evar. *)
  Control.focus 2 2 build_func ;
  (* Normalize the instance before solving the original goal. *)
  Control.focus 1 1 (fun () => 
    let ev_term := mk_evar ev [| |] in
    let result := eval_cbv RedFlags.all ev_term in 
    exact $result).

(*************************************************************************************)
(** *** Examples.  *)
(*************************************************************************************)

Instance option_functor : Functor option. derive_functor (). Defined.
Instance list_functor : Functor list. derive_functor (). Defined.

Inductive tree A :=
  | Leaf : A -> tree A
  | Node : bool -> list (option (tree A)) -> tree A.
Instance tree_functor : Functor tree. derive_functor (). Defined.

Inductive tree2 A :=
  | T : list (tree (option A)) -> tree2 A.
Instance tree2_functor : Functor tree2. derive_functor (). Defined.