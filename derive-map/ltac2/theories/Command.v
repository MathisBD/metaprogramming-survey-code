From Ltac2 Require Import Ltac2 Printf.

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
  
(* Smart constructor for [Constr.Unsafe.App]. *)
Ltac2 mk_app (f : constr) (args : constr array) : constr := 
  Constr.Unsafe.make (Constr.Unsafe.App f args).

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

(*Import Constr Unsafe.

Inductive myind A :=
  | M1 : A -> myind A
  | M2 : A -> A -> A -> myind A.

Ltac2 Eval 
  let x := '(match M1  with nil => nil | cons x l => cons x l end) in 
  match kind x with 
  | Case _ _ _ _ ctrs => printf "c1 : %t" (Array.get ctrs 0) ; printf "c2 : %t" (Array.get ctrs 1)
  | _ => ()
  end.*)

(* Decide whether to apply [f] or not to an argument. All arguments are at the same depth. *)
Ltac2 build_arg (ind : inductive) a b f (arg : constr) (arg_ty : constr) : constr :=
  if Constr.equal a arg_ty then mk_app f [| arg |] else arg.

Ltac2 build_branch (ind : inductive) a b f (ctr : constructor) : constr :=
  (* Get the argument types of the constructor. *)
  let c := Env.instantiate (Std.ConstructRef ctr) in
  let (arg_tys, ret_ty) := decomp_prod (Constr.type c) in 
  (* Remove the first argument (which is the uniform parameter).
     [n] is the number of remaining arguments. *)
  let n := Int.sub (Array.length arg_tys) 1 in
  let arg_tys := Array.sub arg_tys 1 n in
  (* Substitute [a]. After this step each arg_ty_i is at depth [i]. *)
  let arg_tys := Array.mapi (fun i => Constr.Unsafe.substnl [a] i) arg_tys in
  let ret_ty := Constr.Unsafe.substnl [a] n ret_ty in
  (* Lower the arguments as needed. *)
  (*let arg_tys := Array.mapi (fun i => Constr.Unsafe.liftn (Int.neg i) 0) arg_tys in
  let ret_ty := Constr.Unsafe.liftn (Int.neg n) 0 ret_ty in*)
  printf "a=%t    b=%t    f=%t" a b f ;
  printf "arg_tys =" ; Array.iter (printf ">>> %t") arg_tys ;
  printf "ret_ty = %t" ret_ty ;
  (* Build the arguments for the resulting application, at depth [n]. *)
  let args := 
    Array.init n (fun i => 
      let arg := mk_rel (Int.sub n i) in
      let arg_ty := Array.get arg_tys i in
      build_arg ind (lift n a) (lift n b) (lift n f) arg (lift (Int.sub n i) arg_ty))
  in
  printf "args =" ; Array.iter (printf ">>> %t") args ;
  (* Build the final branch. *)
  let branch := Array.fold_right 
    (fun ty body => 
      (* No need to lift the type here. *)
      mk_lambda (Constr.Binder.unsafe_make None Constr.Binder.Relevant ty) body) 
    arg_tys
    (mk_app c (Array.append [| lift n b |] args))   
  in 
  printf "BRANCH %t" branch ;
  branch.

Ltac2 build_map (ind : inductive) : constr := 
  let i := Env.instantiate (Std.IndRef ind) in
  (* Bind the variables. *)
  let a := Constr.Unsafe.make (Constr.Unsafe.Rel 4) in
  let b := Constr.Unsafe.make (Constr.Unsafe.Rel 3) in
  let f := Constr.Unsafe.make (Constr.Unsafe.Rel 2) in
  let x := Constr.Unsafe.make (Constr.Unsafe.Rel 1) in
  (* Get the list of constructors of the inductive type. *)
  let ind_data := Ind.data ind in
  let constructors := Array.init (Ind.nconstructors ind_data) (Ind.get_constructor ind_data) in
  (* If we could quote open terms : '(fun _ => $i $b). *)
  let match_ret := 
    mk_lambda 
      (Constr.Binder.unsafe_make None Constr.Binder.Relevant (mk_app i [| a |])) 
      (mk_app i [| lift1 b |]) 
  in
  printf "Match ret=" ; printf "%t" match_ret ;
  (* Generate the match body. *)
  let body := 
    Constr.Unsafe.make (Constr.Unsafe.Case
      (Constr.Unsafe.case ind) 
      (match_ret, Constr.Binder.Relevant) 
      Constr.Unsafe.NoInvert   
      x 
      (Array.map (build_branch ind a b f) constructors))
  in
  printf "Match body =";
  printf "%t" body ;
  (* Generate the final function. *)
  '(fun (A B : Type) (f : A -> B) (x : $i A) => $body).

(* DeriveMap command entry point. It takes as input the name of an inductive 
   and returns the corresponding mapping function. *)
Ltac2 derive_map (ind_name : string) : unit := 
  (* Error handling. *)
  let fail msg :=
    Control.throw (Invalid_argument (Some (Message.of_string msg)))
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
  printf "Mapping function : %t" f ;
  (* Typecheck the result to make sure. *).

(***********************************************************************************)
(* Testing. *)

Inductive trivial (A : Type) : Type := 
  | T1 : A -> trivial A.

Inductive bunch A :=
  | One : A -> bunch A
  | Two : A -> A -> bunch A
  | Tagged : bool -> A -> bool -> bunch A.

Ltac2 Eval derive_map "bunch".