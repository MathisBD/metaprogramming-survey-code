(* Old version (broken now) that manipulates open terms. *)

From Ltac2 Require Import Ltac2 Printf.
From Coq Require List.

(** Utils. *)

Module StringUtils.

(* [init n f] creates the string with characters [f 0], [f 1], ..., [f (n-1)]. *)
Ltac2 init (n : int) (f : int -> char) : string :=
  let str := String.make n (Char.of_int 0) in 
  let rec loop i :=
    if (Int.ge i 0) then String.set str i (f i) ; loop (Int.sub i 1) else ()
  in
  loop (Int.sub n 1) ; str.

(* [sub str ofs len] returns the substring of [str] starting at [ofs] of size [len]. *)
Ltac2 sub (str : string) (ofs : int) (len : int) : string :=
  init len (fun i => String.get str (Int.add ofs i)).

(* [split_on_char c str] splits the string [str] on the char [c].
   Examples with c the dot '.' character : 
   >> split_on_char c "split.me" = ["split"; "me"]
   >> split_on_char c ".lots...of.dots.." = [""; "lots"; ""; ""; "of"; "dots"; ""; ""]
   >> split_on_char c "" = [""]
   In particular the resulting list is always non-empty. 
*)
Ltac2 split_on_char (c : char) (str : string) : string list :=
  let n := String.length str in
  (* Invariant : 
     - i is the start of the current string (i >= 0).
     - k is the length of the current string (k >= 0). *)
  let rec loop i k acc :=
    if Int.ge (Int.add i k) n then 
      sub str i k :: acc
    else if Char.equal (String.get str (Int.add i k)) c then 
      loop (Int.add i (Int.add k 1)) 0 (sub str i k :: acc)
    else 
      loop i (Int.add k 1) acc  
  in
  List.rev (loop 0 0 []).

End StringUtils.

Module OptionUtils.

(* The type says everything. *)
Ltac2 rec sequence (xs : 'a option list) : 'a list option :=
  match xs with 
  | [] => Some []
  | None :: _ => None
  | Some x :: xs => 
      match sequence xs with 
      | None => None 
      | Some xs => Some (x :: xs)
      end
  end.

End OptionUtils.

(* Lift all free variables by a given amount. *)
Ltac2 lift (n : int) (t : constr) : constr := Constr.Unsafe.liftn n 0 t.

(* Lift all free varaibles by 1. *)
Ltac2 lift1 (t : constr) : constr := Constr.Unsafe.liftn 1 0 t.

(* Smart constructor for [Constr.Unsafe.Rel]. *)
Ltac2 mk_rel (n : int) : constr :=
  Constr.Unsafe.make (Constr.Unsafe.Rel n).

(* Smart constructor for [Constr.Unsafe.Lambda]. *)
Ltac2 mk_lambda (bind : binder) (body : constr) : constr := 
  Constr.Unsafe.make (Constr.Unsafe.Lambda bind body).

(* Smart constructor for [Constr.Unsafe.Prod]. *)
Ltac2 mk_prod (bind : binder) (body : constr) : constr := 
  Constr.Unsafe.make (Constr.Unsafe.Prod bind body).

(* Smart constructor for [Constr.Unsafe.App]. 
   It handles gracefully the edge cases where [f] is already an application or [args] is empty. *)
Ltac2 mk_apps (f : constr) (args : constr array) : constr := 
  if Int.equal (Array.length args) 0 then f 
  else 
    match Constr.Unsafe.kind f with 
    | Constr.Unsafe.App f fargs => Constr.Unsafe.make (Constr.Unsafe.App f (Array.append fargs args))
    | _ => Constr.Unsafe.make (Constr.Unsafe.App f args)
    end.

(* Smart constructor for [Constr.Unsafe.App]. 
   It handles gracefully the edge cases where [f] is already an application. *)
Ltac2 mk_app (f : constr) (arg : constr) : constr := mk_apps f [| arg |].
  
(* Smart constructor to make a single fixpoint (not mutually recursive fixpoints).
   It takes as input :
   - The index of the structurally recursive argument (starting at 0).
   - The binder for the fixpoint parameter (the recursive function).
   - The body of the fixpoint, which has access to the fixpoint parameter as [Rel 1].
*)
Ltac2 mk_fix (struct_arg_idx : int) (binder : binder) (body : constr) : constr :=
  Constr.Unsafe.make (Constr.Unsafe.Fix [| struct_arg_idx |] 0 [| binder |] [| body |]).

(* Unify two terms t1 and t2 *when no goal is focussed*. 
   Returns a boolean indicating whether unification succeeded. 

   For some reason Ltac2 unification requires that some goal be focussed :
   see https://github.com/coq/coq/issues/18021 for more info.
   This is not the case in our setting : the workaround is to create an artificial goal
   just for unification. This is probably quite slow, which doesn't matter for us.
*)
Ltac2 unify_ (t : constr) (u : constr) : bool :=
  (* Create an evar. *)
  let g := 
    match Constr.Unsafe.kind '_ with 
    | Constr.Unsafe.Evar ev _ => ev 
    | _ => Control.throw Assertion_failure
    end 
  in 
  (* Focus an arbitrary goal. *)
  Control.new_goal g ;
  Control.focus 1 1 (fun () => 
    (* Call unification. *)
    Control.plus 
      (fun () => Unification.unify_with_current_ts t u ; true))
      (fun exn => match exn with Internal _ => false | _ => Control.zero exn end).  

(* Check if [x] occurs in [t]. For now we only handle the case where [x] is a de Bruijn index. *)
Ltac2 occurs (x : constr) (t : constr) : bool := 
  match Constr.Unsafe.kind x with 
  | Constr.Unsafe.Rel n => 
    (* For some reason the behaviour of [occurn] is the opposite of what it should be. *)
    (* See also https://github.com/coq/coq/issues/19602 *)
    Bool.neg (Constr.Unsafe.occurn n t)
  | _ =>
    let msg := Message.of_string "occurs" in 
    Control.throw (Invalid_argument (Some msg))  
  end.

(* Copy [t] with [a] replaced by [b]. *)
Ltac2 rec copy_with (a : constr) (b : constr) (t : constr) : constr := 
  if Constr.equal a t then b else Constr.Unsafe.map (copy_with a b) t.

(**************************************************************************************)

(* Find the global reference attached to a name. 
   Fails if the name is invalid or is ambiguous. *)

(* Decode a qualified name to a list of identifiers. *)
Ltac2 decode_name (name : string) : ident list option :=
  (* The dot '.' character. *)
  let dot_char := Char.of_int 46 in
  let parts := StringUtils.split_on_char dot_char name in
  (* We take care that some identifiers might be invalid. *)
  OptionUtils.sequence (List.map Ident.of_string parts).
  
(* [decomp_prod T] returns the argument types and return type of T.
   If T is of the form [forall x1 : A1, forall x2 : A2, ... forall xn : An, R],
   the arguments are [A1; ..., An] and the return type is R (which is not itself a product). *)
Ltac2 decomp_prod (ty : constr) : constr array * constr := 
  let rec loop acc ty := 
    match Constr.Unsafe.kind ty with 
    | Constr.Unsafe.Prod binder ret => loop (Constr.Binder.type binder :: acc) ret
    | _ => List.rev acc, ty
    end
  in 
  let (args, ret) := loop [] ty in
  Array.of_list args, ret.


(* This module implements rules to lift mappings, and a small algebra of 
   combinators to manipulate these rules. *)
Module LiftRule.

(* A lifting rule [rule a b fab t u] lifts the function [f : a -> b] to a function [ftu : t -> u].
   It is expected that [u] is equal to [t] with [a] replaced by [b]. *)
Ltac2 Type t := constr -> constr -> constr -> constr -> constr -> constr option.

(* A base rule which always fails. *)
Ltac2 fail : t :=
  fun _a _b _fab _t _u => None.

(* A rule which handles the cases where there is no lifting to be done. *)
Ltac2 base_apply : t :=
  fun a b fab t u =>
    printf "RULE APPLY" ;
    if Bool.and (Constr.equal a t) (Constr.equal b u) 
    then Some fab
    else None.

(* A rule which handles the cases where [t] does not contain [a] (and thus [u] does not contain [b]). *)
Ltac2 base_id : t :=
  fun a _b _fab t _u =>
    printf "RULE ID" ;
    if Bool.neg (occurs a t)
    then 
      (* We return the identity on type [t], which has type [t -> u] since in this case [u] is equal to [t]. *)
      let id_t := mk_lambda (Constr.Binder.unsafe_make None Constr.Binder.Relevant t) (mk_rel 1) in
      Some id_t
    else None.

(* [or r1 r2] tries [r1] and if it fails applies [r2]. *)
Ltac2 or (r1 : t) (r2 : t) : t :=
  fun a b fab t u => 
    match r1 a b fab t u with 
    | Some ftu => Some ftu
    | None => r2 a b fab t u
    end.

(* [any rs] tries the rules in [rs] in order from first to last and returns the first success. *)
Ltac2 any (rs : t list) : t :=
  match rs with 
  | [] => fail
  | r :: rs => List.fold_left or r rs
  end.

Ltac2 abstract (x : constr) (ty : constr) (body : constr) : constr :=
  mk_lambda 
    (Constr.Binder.unsafe_make None Constr.Binder.Relevant ty) 
    (copy_with x (mk_rel 1) body).

(* [beta_root t] check if [t] contains a beta redex at its root :
   - if yes it contracts it.
   - otherwise it returns [t] unchanged. 
   It lifts the argument of the redex as needed. *)
Ltac2 beta_root (t : constr) : constr :=
  match Constr.Unsafe.kind t with 
  | Constr.Unsafe.App f args =>
    match Constr.Unsafe.kind f with 
    | Constr.Unsafe.Lambda _ body => 
       let remaining_args := Array.sub args 1 (Int.sub (Array.length args) 1) in
       mk_apps (Constr.Unsafe.substnl [Array.get args 0] 0 body) remaining_args
    | _ => t
    end
  | _ => t 
  end.

(* An example rule for lists. *)
Ltac2 list_rule (rec_rule : t) : t := 
  fun a b fab t _u =>
    printf "RULE LIST" ;
    let alpha := '(_ : Type -> Type) in
    let t' := abstract a 'Type t in 
    let pat := '(fun a => list ($alpha a)) in
    if unify_ t' pat  then
      printf "SUCCESS !" ;
      let x := beta_root (mk_app alpha a) in 
      let y := beta_root (mk_app alpha b) in
      printf "Recursing with a=%t b=%t fab=%t x=%t y=%t" a b fab x y ;
      match rec_rule a b fab x y with
      | None => None 
      | Some f => Some (mk_apps '(List.map) [| mk_app alpha a ; mk_app alpha b ; f |])
      end
    else None.

(* Fixpoint operation on lift rules. 
   Since Ltac2 uses an eager evaluation strategy, I have to explicitly eta-expand the 
   definition of [fix_], otherwise using it will loop forever. This is also the reason
   why I use this function instead of Ltac2's let-rec statement : so that [fix_] handles 
   the eta-expansion and the code that uses [fix_] can forget about these details. *)
Ltac2 rec fix_ (f : t -> t) : t := 
  fun a b fab t u => f (fix_ f) a b fab t u.

End LiftRule.

(* Lift a mapping [f : a -> b] to operate on the argument [arg] of type [t].
   The parameter [map] is the fixpoint parameter of type [forall A B, (A -> B) -> I A -> I B]. *)
Ltac2 rec build_arg (ind : inductive) map a b f (arg : constr) (t : constr) : constr :=
  (* Replace [a] with [b] in [arg_ty]. *)
  let u := copy_with a b t in
  printf "BUILD_ARGS a=%t  b=%t  t=%t  u=%t" a b t u ; 
  (* Custom rule to lift from [a -> b] to [i a -> i b] using [map]. *)
  let map_rule a b fab t u :=
    printf "RULE MAP" ;
    let i := Env.instantiate (Std.IndRef ind) in
    if Bool.and (Constr.equal t (mk_app i a)) (Constr.equal u (mk_app i b))
    then Some (mk_apps map [| a ; b ; fab |])
    else None
  in
  (* Build the complete lifting rule we will be using. *)
  let rule := 
    LiftRule.fix_ (fun rule => 
      LiftRule.any 
        [ LiftRule.base_apply 
        ; LiftRule.base_id 
        ; LiftRule.list_rule rule
        ; map_rule
        ])
  in
  (* Apply the rule. *)
  match rule a b f t u with 
  | None => Control.throw (Tactic_failure (Some (Message.of_constr t)))
  | Some ftu => mk_app ftu arg
  end.

Ltac2 build_branch (ind : inductive) map a b f (ctr : constructor) : constr :=
  (* Get the argument types of the constructor. *)
  let c := Env.instantiate (Std.ConstructRef ctr) in
  let (arg_tys, _) := decomp_prod (Constr.type c) in 
  (* Remove the first argument (which is the uniform parameter).
     [n] is the number of remaining arguments. *)
  let n := Int.sub (Array.length arg_tys) 1 in
  let arg_tys := Array.sub arg_tys 1 n in
  (* Substitute [a]. After this step each arg_ty_i is at depth [i]. *)
  let arg_tys := Array.mapi (fun i => Constr.Unsafe.substnl [a] i) arg_tys in
  (* Build the arguments for the resulting application, at depth [n]. *)
  let args := 
    Array.init n (fun i => 
      let arg := mk_rel (Int.sub n i) in
      let arg_ty := Array.get arg_tys i in
      build_arg ind (lift n map) (lift n a) (lift n b) (lift n f) arg (lift (Int.sub n i) arg_ty))
  in
  (* Build the final branch. *)
  let branch := Array.fold_right 
    (fun ty body => 
      (* No need to lift the type here. *)
      mk_lambda (Constr.Binder.unsafe_make None Constr.Binder.Relevant ty) body) 
    arg_tys
    (mk_apps (mk_app c (lift n b)) args)  
  in 
  branch.

Ltac2 build_map (ind : inductive) : constr := 
  let i := Env.instantiate (Std.IndRef ind) in
  (* Bind the variables. *)
  let map := mk_rel 5 in
  let a := mk_rel 4 in
  let b := mk_rel 3 in
  let f := mk_rel 2 in
  let x := mk_rel 1 in
  (* Get the list of constructors of the inductive type. *)
  let ind_data := Ind.data ind in
  let constructors := Array.init (Ind.nconstructors ind_data) (Ind.get_constructor ind_data) in
  (* If we could quote open terms : '(fun _ => $i $b). *)
  let match_ret := 
    mk_lambda 
      (Constr.Binder.unsafe_make None Constr.Binder.Relevant (mk_app i a)) 
      (mk_app i (lift1 b)) 
  in
  (* Generate the match body. *)
  let body := 
    Constr.Unsafe.make (Constr.Unsafe.Case
      (Constr.Unsafe.case ind) 
      (match_ret, Constr.Binder.Relevant) 
      Constr.Unsafe.NoInvert   
      x 
      (Array.map (build_branch ind map a b f) constructors))
  in
  (* Generate the final function. *)
  '(fix map (A B : Type) (f : A -> B) (x : $i A) : $i B := $body).

(* DeriveMap command entry point. It takes as input the name of an inductive 
   and returns the corresponding mapping function. *)
Ltac2 derive_map (ind_name : string) : constr := 
  (* Error handling. *)
  let fail msg :=
    Control.throw (Tactic_failure (Some (Message.of_string msg)))
  in
  (* Find the inductive in the environment. *)
  let ind := 
    match decode_name ind_name with 
    | None => fail "Invalid identifier !"
    | Some ids => 
      match Env.expand ids with 
      | [] => fail "Unknown reference !"
      | Std.IndRef ind :: _ => ind
      | _ :: _ => fail "Not an inductive !"
      end
    end
  in 
  let i := Env.instantiate (Std.IndRef ind) in
  (* Check the inductive has exactly one parameter of type [Type]. *)
  lazy_match! Constr.type i with 
  | Type -> _ => ()
  | _ => fail "Inductive should have exactly one parameter of type [Type]"
  end ;
  (* Build the mapping function. *)
  let f := build_map ind in
  printf "Result :" ; printf "%t" f ;
  (* Typecheck the result to make sure. *)
  let f := 
    match Constr.Unsafe.check f with 
    | Val f => f
    | Err _ => fail "Resulting function does not typecheck"
    end
  in f.

(***********************************************************************************)
(* Testing. *)

Inductive trivial (A : Type) : Type := 
  | T1 : list A -> trivial A.

Ltac2 Eval derive_map "trivial".


Inductive bunch A :=
  | One : A -> bunch A
  | Two : A -> bunch A -> bunch A
  | Tagged : bool -> list A -> bool -> bunch A.

Ltac2 Eval derive_map "bunch".