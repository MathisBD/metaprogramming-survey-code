(**************************************************************************)
(* This version only works for inductives which have exactly one parameter, 
   which moreover has to be *uniform*. *)
(**************************************************************************)

From elpi Require Import elpi.

Elpi Command DeriveMap.
Elpi Accumulate lp:{{

% Command entry point.  
main [str IndName] :- std.do! [
  % Locate the inductive type.
  std.assert! (coq.locate IndName (indt Ind)) "Could not find inductive type.",
  % Check the inductive has exactly one parameter.
  std.assert! 
    (coq.env.indt-decl Ind (parameter _ _ ParamTy _\ inductive _ tt _ _))
    "This command only supports inductive types with exactly one parameter.",
  % Build the map function.
  pi a\ do-map Ind ParamTy F,
  % Add the function to the Coq global environment.
  Name is IndName ^ "_map",
  coq.ensure-fresh-global-id Name FName,
  coq.env.add-const FName F _ @transparent! C,
  coq.say "Added function under name" C,
  % Set implicit arguments for the function.
  % For some reason we can't do this while building the function.
  coq.arguments.set-implicit (const C) [[ maximal, maximal, explicit, explicit ]]
].

% ---------------------------------------------------------------------------------------

pred do-map 
  i:inductive,  % The inductive type (with parameters).
  i:term,       % The type of the inductive parameter.
  o:term.       % The map function we are building.

% We build a recursive function (a fixpoint).
do-map I PTy 
  {{ fix map (A : lp:PTy) (B : lp:PTy) (f : A -> B) (x : lp:GI A) {struct x} : lp:GI B := lp:(Match map A B f x) }} 
:- std.do! [
  GI = global (indt I),
  @pi-decl `map` _ map\
  @pi-decl `a` PTy a\ 
  @pi-decl `b` PTy b\ 
  @pi-decl `f` {{ lp:a -> lp:b }} f\
  @pi-decl `x` {{ lp:GI lp:a }} x\
    do-match I map a b f x (Match map a b f x)
]. 


% ---------------------------------------------------------------------------------------

pred do-match 
  i:inductive, % I the inductive type.
  i:term, % The recursive map function.
  i:term, % A the value of the parameter we map *from*.
  i:term, % B the value of the parameter we map *to*.
  i:term, % f : A -> B the mapping function.
  i:term, % x : I A the input.
  o:term. % The resulting match statement.

do-match I Map A B F X Match :-
  coq.mk-app (global (indt I)) [A] IA,
  coq.mk-app (global (indt I)) [B] IB,
  coq.build-match 
    X
    IA
    (_\_\_\r\ r = IB)
    (do-branch I Map A B F)
    Match. 

% ---------------------------------------------------------------------------------------

pred do-branch 
  i:inductive, % I the inductive type.
  i:term, % The recursive map function.
  i:term, % A the value of the parameter we map *from*.
  i:term, % B the value of the parameter we map *to*.
  i:term, % f : A -> B the mapping function.
  i:term, % The branch constructor (applied to the parameters).
  i:term, % ???
  i:list term, % The arguments of the constructor (without the parameters).
  i:list term, % The types of each arguments.
  o:term. % The resulting branch.

do-branch I Map A B F CA _ Args ArgsTy Branch :- std.do! [
  % Decide for each arg whether we leave it as is, apply F or Map to it or if it can't be handled.
  std.map2 Args ArgsTy (do-branch.aux I Map A B F) MappedArgs, 
  % Change A with B in the constructor.
  (copy A B => copy CA CB),
  % Apply the constructor to the new arguments.
  coq.mk-app CB MappedArgs Branch
].

% An argument of type [A] : apply the mapping function [F].
do-branch.aux I Map A B F Arg A {{ lp:F lp:Arg }} :- !.
% An argument of type [I A] : apply the recursive function [Map].
do-branch.aux I Map A B F Arg ArgTy NewArg :- 
  coq.mk-app (global (indt I)) [A] ArgTy,
  !, coq.mk-app Map [A, B, F, Arg] NewArg.
% Otherwise check if the type of the argument contains [A] :
% if yes we fail otherwise we keep the argument as is.
do-branch.aux _ _ A _ _ Arg ArgTy NewArg :- 
  (occurs A ArgTy, coq.error "Can't map over argument of type [" { coq.term->string ArgTy } "]")
  ; NewArg = Arg.

% ---------------------------------------------------------------------------------------

}}.

Elpi Typecheck.

(**************************************************************************)
(* Testing. *)

Inductive double B := Double : B -> B -> double B.
Inductive tree A := 
  | Leaf : A -> bool -> tree A
  | Node : tree A -> A -> tree A -> tree A.

Definition size := fix size {A : Type} (t : tree A) : nat := 
  match t with 
  | Leaf _ _ _ => 1
  | Node _ t1 _ t2 => size t1 + size t2
  end.

Elpi DeriveMap tree.
Elpi DeriveMap list.

Print list_map.

Definition t := Node _ (Leaf _ 1 true) 2 (Node _ (Leaf _ 3 false) 4 (Leaf _ 5 true)).
Eval compute in t.
Eval compute in tree_map (Nat.add 40) t.

