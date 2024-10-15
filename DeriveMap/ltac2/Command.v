(* New version which does NOT manipulate open terms 
   (or at least not more than necessary). *)

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

(* Throw a fatal [Tactic_failure] exception with the given message. *)
Ltac2 tactic_fail (msg : string) : 'a :=
  Control.throw (Tactic_failure (Some (Message.of_string msg))).

(* Lift all free variables by a given amount. *)
Ltac2 lift (n : int) (t : constr) : constr := Constr.Unsafe.liftn n 0 t.

(* Lift all free varaibles by 1. *)
Ltac2 lift1 (t : constr) : constr := Constr.Unsafe.liftn 1 0 t.

(* Smart constructor for [Constr.Unsafe.Rel]. *)
Ltac2 mk_rel (n : int) : constr :=
  Constr.Unsafe.make (Constr.Unsafe.Rel n).

(* Smart constructor for [Constr.Unsafe.Var]. *)
Ltac2 mk_var (i : ident) : constr :=
  Constr.Unsafe.make (Constr.Unsafe.Var i).

(* Smart constructor for [Constr.Unsafe.Lambda]. 
   Does not perform term lifting. *)
Ltac2 mk_lambda (bind : binder) (body : constr) : constr := 
  Constr.Unsafe.make (Constr.Unsafe.Lambda bind body).

(* Smart constructor for [Constr.Unsafe.Prod]. 
   Does not perform term lifting. *)
Ltac2 mk_prod (bind : binder) (body : constr) : constr := 
  Constr.Unsafe.make (Constr.Unsafe.Prod bind body).

(* Smart constructor for [Constr.Unsafe.Prod] when the binder is anonymous. 
   Does not perform term lifting. *)
Ltac2 mk_arrow (t1 : constr) (t2 : constr) : constr := 
  Constr.Unsafe.make 
    (Constr.Unsafe.Prod (Constr.Binder.unsafe_make None Constr.Binder.Relevant t1) t2).

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

(* Beta reduce a term. Might not work on open terms. *)
Ltac2 beta_red (t : constr) : constr := Std.eval_cbv RedFlags.beta t.

(* Unify two terms t1 and t2. 
   It only works if t1 and t2 are closed terms (contain no free de Bruijn index).
   Returns a boolean indicating whether unification succeeded. 

   For some reason Ltac2 unification requires that some goal be focussed :
   see https://github.com/coq/coq/issues/18021 for more info.
*)
Ltac2 unify_ (t : constr) (u : constr) : bool :=
  (* Call unification. *)
  Control.plus 
    (fun () => Unification.unify_with_current_ts t u ; true)
    (fun exn => match exn with Internal _ => false | _ => Control.zero exn end).  

(* Many Ltac2 functions require a goal to be focuessed. This is not the case in our setting :
   the workaround is to create an artificial goal and focus it. *)
Ltac2 with_goal (f : unit -> 'a) : 'a :=
  (* Create an evar. *)
  let g := 
    match Constr.Unsafe.kind '_ with 
    | Constr.Unsafe.Evar ev _ => ev 
    | _ => tactic_fail "unify_"
    end 
  in 
  (* Create a goal and focus it. *)
  Control.new_goal g ;
  Control.focus 1 1 f.
  

(**************************************************************************************)

(* Finds the global reference attached to a name. 
   Fails if the name is invalid or is ambiguous. *)

(* Decode a qualified name to a list of identifiers. *)
Ltac2 decode_name (name : string) : ident list option :=
  (* The dot '.' character. *)
  let dot_char := Char.of_int 46 in
  let parts := StringUtils.split_on_char dot_char name in
  (* We take care that some identifiers might be invalid. *)
  OptionUtils.sequence (List.map Ident.of_string parts).

(* This module implements rules to lift mappings, and a small algebra of 
   combinators to manipulate these rules. *)
Module LiftRule.

(* A lifting rule lifts a function [f : a -> b] to a function [f' : t a -> t b].
   
   Formally we view a lifting rule as a (partial) mapping from a type former [T : Type -> Type]
   to a function [F : MapTy -> forall A B, (A -> B) -> T A -> T B], 
   where MapTy is the type of the recursive mapping function.

   Both [T] and [F] are closed terms.
*)
Ltac2 Type t := constr (* T *) -> constr option (* F *).
 
(* A base rule which always fails. *)
Ltac2 fail : t := fun _ => None.

(* A rule which handles the cases where there is no lifting to be done. *)
Ltac2 base_apply : t :=
  fun t =>
    printf "RULE APPLY on %t" t ;
    lazy_match! t with 
    | fun (A : Type) => A => printf "SUCCESS" ; Some '(fun _ (A B : Type) f => f)
    | _ => printf "FAIL" ; None 
    end.

(* A rule which handles the cases where [t] does not contain [a] (and thus [u] does not contain [b]). *)
Ltac2 base_id : t :=
  fun t =>
    printf "RULE ID on %t" t ;
    lazy_match! t with 
    | fun (A : Type) => ?_body => printf "SUCCESS" ; Some '(fun _ (A B : Type) (f : A -> B) (x : $t A) => x)
    | _ => printf "FAIL" ; None
    end.

(* [or r1 r2] tries [r1] and if it fails applies [r2]. *)
Ltac2 or (r1 : t) (r2 : t) : t :=
  fun t => 
    match r1 t with 
    | Some f => Some f
    | None => r2 t
    end.

(* [any rs] tries the rules in [rs] in order from first to last and returns the first success. *)
Ltac2 any (rs : t list) : t :=
  match rs with 
  | [] => fail
  | r :: rs => List.fold_left or r rs
  end.

(* An example rule for lists. *)
Ltac2 list_rule (rec_rule : t) : t := 
  fun t =>
    printf "RULE LIST on %t" t ;
    (* Check [t] is of the right form. *)
    let u := '(_ : Type -> Type) in 
    let success := unify_ t '(fun (A : Type) => list ($u A)) in
    if success then 
      printf "RECURSING with %t" u ;
      (* Recurse with [u]. *)
      match rec_rule u with 
      | Some fu => printf "SUCCESS" ; Some '(fun map (A B : Type) (f : A -> B) => @List.map ($u A) ($u B) ($fu map A B f))
      | None => printf "FAIL" ; None
      end 
    else (printf "FAIL" ; None).

Ltac2 Eval with_goal (fun () =>
  let i := '(_ : Type -> Type) in
  let success := 
    unify_ 
      '(forall A B : Type, (A -> B) -> (fun _ => list A) B -> list B) 
      '(forall A B : Type, (A -> B) -> $i A -> $i B)
  in 
  if success then printf "SUCCESS %t" i else printf "FAIL").

Ltac2 make_rule (func : constr) (rec_rule : t) : t :=
  (* Make sure [func] has the right type. *)
  printf "make_rule TYPE= %t" (Constr.type func) ;
  let i := '(_ : Type -> Type) in
  if unify_ (Constr.type func) '(forall (A B : Type), (A -> B) -> $i A -> $i B) then 
    (* Build the rule *)
    fun t =>
      printf "CUSTOM RULE" ;
      (* Check the head of [t] is build using [i]. *)
      let u := '(_ : Type -> Type) in
      if unify_ t '(fun A => $i ($u A)) then 
        printf "RECURSING with %t" u ;
        (* Recurse with [u]. *)
        match rec_rule u with 
        | Some fu => 
          printf "SUCCESS" ; 
          Some '(fun map (A B : Type) (f : A -> B) => $func ($u A) ($u B) ($fu map A B f))
        | _ => printf "FAIL" ; None
        end
      else (printf "FAIL" ; None)
  else tactic_fail "make_rule : not a mapping function".

(* Fixpoint operation on lift rules. 
   Since Ltac2 uses an eager evaluation strategy, I have to explicitly eta-expand the 
   definition of [fix_], otherwise using it will loop forever. This is also the reason
   why I use this function instead of Ltac2's let-rec statement : so that [fix_] handles 
   the eta-expansion and the code that uses [fix_] can forget about these details. *)
Ltac2 rec fix_ (f : t -> t) : t := 
  fun t => f (fix_ f) t.

End LiftRule.

(* Replace all occurences of [a] with [b] in [t], without performing any lifting. *)
Ltac2 rec replace_subterm (a : constr) (b : constr) (t : constr) : constr := 
  if Constr.equal a t then b else Constr.Unsafe.map (replace_subterm a b) t.

(* [constructor_args ctr] returns the types of the arguments of [ctr].
   This assumes the corresponding inductive has exactly one uniform parameter,
   and returns the argument types of [ctr] as a function of this parameter. 
   
   This function performs a bit of term surgery.
*)
Ltac2 constructor_arg_types (ctr : constructor) : constr list := 
  (* Get the type of the constructor. *)
  let cty := Constr.type (Env.instantiate (Std.ConstructRef ctr)) in
  (* Peel off the first argument type. *)
  match Constr.Unsafe.kind cty with 
  | Constr.Unsafe.Prod binder_a cty => 
    (* Collect the remaining argument types while abstracting over the first one. *)
    let rec loop i acc cty :=
      match Constr.Unsafe.kind cty with 
      | Constr.Unsafe.Prod binder cty => 
        (* Get the argument type. *)
        let arg_ty := Constr.Binder.type binder in
        (* Check the argument type does not depend on any previous argument 
           (apart from the first one which is the inductive parameter). 
           For some reason Constr.Unsafe.occur_between has its meaning reversed :
           see https://github.com/coq/coq/issues/19602 
           If this is fixed in the future, remove [Bool.neg] in the test below. *)
        if Bool.neg (Constr.Unsafe.occur_between 1 i arg_ty) then 
          tactic_fail "constructor_arg_types : dependent argument"
        else 
          (* Abstract over the inductive parameter. *)
          let arg_ty := 
            mk_lambda binder_a 
              (replace_subterm (mk_rel (Int.add i 1)) (mk_rel 1) arg_ty) 
          in
          (* Recurse to gather the remaining arguments. *)
          loop (Int.add i 1) (arg_ty :: acc) cty
      | _ => List.rev acc 
      end
    in 
    loop 0 [] cty
  | _ => tactic_fail "constructor_arg_types : constructor type is not a product"
  end.
      

Ltac2 string_of_int (i : int) : string := Message.to_string (Message.of_int i).

(* The resulting branch abstracts over [map], [A], [B] and [f]. *)
Ltac2 build_branch (ctr : constructor) : constr :=
  (* Get the argument types of the constructor. *)
  let arg_tys := constructor_arg_types ctr in 
  let n := List.length arg_tys in
  (* Create [n] variables for the arguments. *)
  let args := List.init n (fun i => mk_rel (Int.sub n i)) in 
  (* Variables for map, A, B and f. *)
  let map := mk_rel (Int.add n 4) in
  let a := mk_rel (Int.add n 3) in 
  let b := mk_rel (Int.add n 2) in 
  let f := mk_rel (Int.add n 1) in 
  (* Apply the correct function to each argument. *)
  let args := List.map2 
    (fun arg arg_ty => 
      (* Custom rule to allow mapping on recursive arguments. *)
      let map_rule t :=
        printf "RULE MAP on %t" t ;
        let i := Env.instantiate (Std.IndRef (Constructor.inductive ctr)) in
        if unify_ t '(fun (A : Type) => $i A) then 
          (printf "SUCCESS" ; Some '(fun map A B f => map A B f))
        else 
          (printf "FAIL" ; None)
      in
      let rule := 
        LiftRule.fix_ (fun rule => 
          LiftRule.any 
            [ LiftRule.base_apply 
            ; LiftRule.base_id 
            ; map_rule 
            ; LiftRule.make_rule '(@List.map) rule]) 
      in
      (* Apply the rule. *)
      match rule arg_ty with 
      | None => Control.throw (Tactic_failure (Some (Message.of_constr arg_ty)))
      | Some f' => mk_apps (beta_red f') [| map ; a ; b ; f ; arg |]
      end)
    args arg_tys
  in
  (* Apply the constructor to the (mapped) arguments. *)
  let apps := mk_apps (Env.instantiate (Std.ConstructRef ctr)) (Array.of_list (b :: args)) in
  (* Bind the arguments of the branch. *)
  let res1 := List.fold_lefti
    (fun i res ty => 
      let a := mk_rel (Int.add i 3) in
      mk_lambda (Constr.Binder.unsafe_make (Some @x) Constr.Binder.Relevant (beta_red (mk_app ty a))) res)
    apps 
    arg_tys
  in
  (* Bind a, b and f. *)
  let res2 :=
  mk_lambda (Constr.Binder.unsafe_make (Some @map) Constr.Binder.Relevant '_)
    (mk_lambda (Constr.Binder.unsafe_make (Some @a) Constr.Binder.Relevant 'Type)
      (mk_lambda (Constr.Binder.unsafe_make (Some @b) Constr.Binder.Relevant 'Type)
        (mk_lambda (Constr.Binder.unsafe_make (Some @f) Constr.Binder.Relevant (mk_arrow (mk_rel 2) (mk_rel 2))) res1)))
  in
  printf "RES2 = %t" (beta_red res2) ; (beta_red res2).
  
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
      (Array.map (fun ctr => beta_red (mk_apps (build_branch ctr) [| map ; a ; b ; f |])) constructors))
  in
  (* Generate the final function. *)
  '(fix map (A B : Type) (f : A -> B) (x : $i A) : $i B := $body).
    
(* DeriveMap command entry point. It takes as input the name of an inductive 
   and returns the corresponding mapping function. *)
Ltac2 derive_map (ind_name : string) : constr := 
  with_goal (fun () => 
    (* Find the inductive in the environment. *)
    let ind := 
      match decode_name ind_name with 
      | None => tactic_fail "Invalid identifier !"
      | Some ids => 
        match Env.expand ids with 
        | [] => tactic_fail "Unknown reference !"
        | Std.IndRef ind :: _ => ind
        | _ :: _ => tactic_fail "Not an inductive !"
        end
      end
    in 
    let i := Env.instantiate (Std.IndRef ind) in
    (* Check the inductive has exactly one parameter of type [Type]. *)
    lazy_match! Constr.type i with 
    | Type -> _ => ()
    | _ => tactic_fail "Inductive should have exactly one parameter of type [Type]"
    end ;
    (* Build the mapping function. *)
    let f := build_map ind in
    printf "Result :" ; printf "%t" f ;
    (* Typecheck the result to make sure. *)
    let f := 
      match Constr.Unsafe.check f with 
      | Val f => f
      | Err _ => tactic_fail "Resulting function does not typecheck"
      end
    in f).

(***********************************************************************************)
(* Testing. *)

(*Inductive trivial (A : Type) : Type := 
  | T1 : A -> trivial A -> trivial A.

Ltac2 Eval derive_map "list".

Inductive bunch A :=
  (*| One : A -> bunch A
  | Two : A -> bunch A -> bunch A*)
  | Tagged : list A -> bunch A.

Ltac2 Eval derive_map "bunch".*)