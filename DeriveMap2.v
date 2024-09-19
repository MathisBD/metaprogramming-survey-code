(**************************************************************************)
(* Same as DeriveMap but more powerful. Still only one parameter though. *)
(**************************************************************************)

From elpi Require Import elpi.

(* We store all the mapping functions found so far in a database,
   which we can extend at will (for instance when deriving a mapping function for
   an inductive, we can add it to the database). *)
Elpi Db map.db lp:{{

% [lift-mapping A B FAB T U FTU] lifts the elementary mapping function [FAB : A -> B]
% to a more complex mapping function [FTU : T -> U].
% It is expected that U is equal to T with A replaced by B.
pred lift-mapping i:term, i:term, i:term, i:term, i:term, o:term.

% Base case : no lifting to do.
lift-mapping A B FAB A B FAB :- !.

% Base case : the type T does not contain A.
lift-mapping A B FAB T U {{ fun t : lp:T => t }} :-not (occurs A T), !.

% More rules will be added below by coq.elpi.accumulate.

%lift-mapping A B FAB {{ list lp:T }} {{ list lp:U }} {{ @List.map lp:T lp:U lp:FTU }} :- 
%  lift-mapping A B FAB T U FTU.

% ----------------------------------------------------------

% Helper function to add a clause to lift-mapping. 
% It takes as input a term [M] and its type of the form [forall (A B : Type), (A -> B) -> T -> U] 
% where T does not contain B, and U is equal to T with A replaced by B. 
% It returns a lift-mapping clause that tells how to lift a function A -> B to a function T -> U. 
% This clause can then e.g. be added to the database using coq.elpi.accumulate.
pred mk-lift-mapping i:term, i:term, o:prop.
mk-lift-mapping M 
  ({{ forall (A B : Type), (A -> B) -> lp:(T A B) -> lp:(U A B) }} as MTy)
  (pi a b fab x y fxy\ lift-mapping a b fab (T x y) (U x y) {{ lp:M lp:x lp:y lp:fxy }} :- lift-mapping a b fab x y fxy) 
:-
  std.assert-ok! (coq.typecheck M MTy) "Invalid type.",
  pi a b\
  % Check T does not contain b.
  not (occurs b (T a b)),
  % Check U is equal to T with a replaced by b.
  (copy a b => copy (T a b) (U a b)).
}}. 


(* Command to extend the map database. *)
Elpi Command AddMap.
Elpi Accumulate Db map.db.
Elpi Accumulate lp:{{
main [trm M] :-
  std.assert-ok! (coq.typecheck M Mty) "Provided function does not typecheck",
  std.assert! (mk-lift-mapping M Mty Rule) "Provided function is not a mapping function",
  coq.elpi.accumulate _ "map.db" (clause _ _ Rule).
}}.
Elpi Typecheck.

Elpi Command DeriveMap.
Elpi Accumulate Db map.db.
Elpi Accumulate lp:{{

% Command entry point.  
main [str IndName] :- std.do! [
  % Locate the inductive type.
  std.assert! (coq.locate IndName (indt Ind)) "Could not find inductive type.",
  % Check the inductive has exactly one parameter (uniform or not).
  (coq.env.indt-decl Ind (parameter _ _ ParamTy _\ inductive _ tt _ _)
  ; coq.env.indt-decl Ind (inductive _ tt (parameter _ _ ParamTy _\ arity _) _)
  ; coq.error "This command only supports inductive types with exactly one parameter."),
  % Check the parameter is a type.
  std.assert! (ParamTy = sort _) "The inductive parameter's type should be a sort.",
  % Build the map function.
  build-map Ind ParamTy F,
  coq.say { coq.term->string F },
  std.assert-ok! (coq.typecheck F _) "Resulting function does not typecheck! Aborting.",
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

pred build-map 
  i:inductive,  % The inductive type (with parameters).
  i:term,       % The type of the inductive parameter.
  o:term.       % The map function we are building.

% We build a recursive function (a fixpoint).
build-map I PTy 
  {{ fix map (A B : lp:PTy) (f : A -> B) (x : lp:GI A) {struct x} : lp:GI B := lp:(Match map A B f x) }} 
:- std.do! [
  GI = global (indt I),
  MapTy = {{ forall (A B : lp:PTy), (A -> B) -> lp:GI A -> lp:GI B }},
  % The fixpoint part. We use the argument [map] to recursively map over subterms of [x] 
  % which are of type [I A]. Technically this amounts to adding a (local) clause to lift-mapping.
  @pi-decl `map` MapTy map\ mk-lift-mapping map MapTy (Rule map), Rule map =>
  % Bind the remaining arguments.
  @pi-decl `a` PTy a\ 
  @pi-decl `b` PTy b\ 
  @pi-decl `f` {{ lp:a -> lp:b }} f\
  @pi-decl `x` {{ lp:GI lp:a }} x\
    % Build the inner match.
    build-match I map a b f x (Match map a b f x)
]. 


% ---------------------------------------------------------------------------------------

pred build-match 
  i:inductive, % I the inductive type.
  i:term, % The recursive map function.
  i:term, % A the value of the parameter we map *from*.
  i:term, % B the value of the parameter we map *to*.
  i:term, % f : A -> B the mapping function.
  i:term, % x : I A the input.
  o:term. % The resulting match statement.

build-match I Map A B F X Match :-
  coq.mk-app (global (indt I)) [A] IA,
  coq.mk-app (global (indt I)) [B] IB,
  coq.build-match 
    X
    IA
    (_\_\_\r\ r = IB)
    (build-branch I Map A B F)
    Match. 

% ---------------------------------------------------------------------------------------

pred build-branch 
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

build-branch I Map A B F CA _ Args ArgsTy Branch :- std.do! [
  % Decide for each arg whether we leave it as is, apply F or Map to it or if it can't be handled.
  std.map2 Args ArgsTy (build-branch.aux A B F) MappedArgs, 
  % Change A with B in the constructor.
  (copy A B => copy CA CB),
  % Apply the constructor to the new arguments.
  coq.mk-app CB MappedArgs Branch
].

build-branch.aux A B F Arg ArgTy NewArg :-
  (copy A B => copy ArgTy NewArgTy),
  coq.say "A =" A ", B =" B ", F =" F ", ArgTy =" ArgTy ", NewArgTy =" NewArgTy,
  lift-mapping A B F ArgTy NewArgTy FArg, 
  !, 
  coq.mk-app FArg [Arg] NewArg.
build-branch.aux A B F Arg ArgTy NewArg :- 
  coq.error "Can't map over argument of type [" { coq.term->string ArgTy } "]".

% ---------------------------------------------------------------------------------------

}}.

Elpi Typecheck.

(**************************************************************************)
(* Testing. *)

Inductive double A := 
  | Double : A -> A -> double A.
Inductive tree A := 
  | Leaf : A -> bool -> tree A
  | Node : list (tree A) -> tree (list A) -> tree A.

Inductive weird A :=
  | Wunit : A -> weird A
  | Wlist : list (weird (double A)) -> weird A.

Elpi DeriveMap double.
Elpi AddMap (@double_map).
Elpi AddMap (@List.map).
Elpi DeriveMap tree.
Elpi DeriveMap weird.

Print double_map.
Print tree_map.
Print weird_map.
