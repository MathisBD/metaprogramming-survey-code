From Ltac2 Require Import Ltac2.

(* Throw a fatal [Tactic_failure] exception with the given message. *)
Ltac2 tactic_fail (msg : string) : 'a :=
  Control.throw (Tactic_failure (Some (Message.of_string msg))).

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
      
