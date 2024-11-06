(** This version does _not_ manipulate open terms (or at least not more than necessary). *)

From Coq Require List.
From Ltac2 Require Import Ltac2 Printf Std.
From DeriveFunctor.Ltac2 Require Import Utils.
From DeriveFunctor Require Import Functor.
 
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

(** [fresh_evar ty] creates a new evar which has type [ty]. *)
Ltac2 fresh_evar (ty : constr) : evar :=
  (* Create the evar. *)
  let ev_term := '_ in 
  let ev := 
    match Constr.Unsafe.kind ev_term with  
    | Constr.Unsafe.Evar ev _ => ev 
    | _ => tactic_fail "copy_goal_evar"
    end
  in 
  (* Set the type of the evar. *)
  Unification.unify_with_current_ts (Constr.type ev_term) ty ;
  ev.

(* Smart constructor for [Constr.Unsafe.Evar]. *)
Ltac2 mk_evar (ev : evar) (args : constr array) : constr :=
  Constr.Unsafe.make (Constr.Unsafe.Evar ev args).

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

