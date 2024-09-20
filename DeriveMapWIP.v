(**************************************************************************)
(* This version deals with multiple parameters. *)
(**************************************************************************)

From elpi Require Import elpi.


Definition prod_map (A B : Type) (f : A -> B) (A' B' : Type) (f' : A' -> B') (x : A * A') : B * B' :=
  match x with 
  | (a, a') => (f a, f' a')
  end.

(* We store all the mapping functions found so far in a database,
   which we can extend at will (for instance when deriving a mapping function for
   an inductive, we can add it to the database). *)
Elpi Db map.db lp:{{

% A small helper function : [copy-with As Bs T U] copies T into U while replacing each Ai with Bi.
pred copy-with i:list term, i:list term, i:term, o:term.
copy-with [] [] T U :- copy T U.
copy-with [A|As] [B|Bs] T U :- copy A B => copy-with As Bs T U.

% [lift-mapping As Bs FABs T U FTU] lifts the elementary mapping functions [FABi : Ai -> Bi]
% to a more complex mapping function [FTU : T -> U].
% It is expected that U is equal to T with each Ai replaced by Bi.
pred lift-mapping i:list term, i:list term, i:list term, i:term, i:term, o:term.

% Try base cases first (T -> U is equal to some Ai -> Bi).
lift-mapping As Bs FABs T U FTU :- lift-mapping.base As Bs FABs T U FTU, !.

lift-mapping.base [A|_] [B|_] [FAB|_] A B FAB :- !.
lift-mapping.base [_|As] [_|Bs] [_|FABs] T U FTU :- lift-mapping.base As Bs FABs T U FTU.

% Other base case : the type T does not contain any Ai.
lift-mapping As Bs FABs T U {{ fun t : lp:T => t }} :- 
  std.forall As (a\ not (occurs a T)), !.

% More rules will be added below by coq.elpi.accumulate.

% Example rule for lists.
%lift-mapping As Bs FABs {{ list lp:T }} {{ list lp:U }} {{ @List.map lp:T lp:U lp:FTU }} :- 
%  lift-mapping As Bs FABs T U FTU.

% Example rule for pairs.
%lift-mapping As Bs FABs ({{ prod lp:X1 lp:X2 }} as (T X1 X2)) ({{ prod lp:Y1 lp:Y2 }} as (U Y1 Y2)) 
%  ({{ prod_map lp:X1 lp:Y1 lp:FXY1 lp:X2 lp:Y2 lp:FXY2 }} as (FTU X1 X2 Y1 Y2 FXY1 FXY2))
%:-
%  lift-mapping As Bs FABs X1 Y1 FXY1,
%  lift-mapping As Bs FABs X2 Y2 FXY2.


% Helper function to add a clause to lift-mapping. 
% It takes as input a term [M] and its type of the form :
%   forall (X1 Y1 : Type), (X1 -> Y1) -> ... -> forall (Xn Yn : Type), (Xn -> Yn) -> (T -> U] 
% where T does not contain any Yi, and U is equal to T with Xs replaced by Ys. 
% It returns a lift-mapping clause that tells how to lift n functions Ai -> Bi to a function T -> U.
% In full generality, this clause has the form :
%   pi as bs fabs\
%     pi x1 y1 fxy1\ 
%     pi x2 y2 fxy2\ lift-mapping as bs fabs x2 y2 fxy2 =>
%     ...
%     pi xn yn fxyn\ 
%     lift-mapping as bs fabs x1 y1 fxy1 =>
% lift-mapping as bs fabs xn yn fxyn =>
%       lift-mapping as bs fabs T U M
% where :
% - T contains x1, ..., xn 
% - U contains y1, ..., yn (in fact U is equal to T with each xi replaced by yi)
% - M is the input mapping function applied to the correct argument (i.e. x1 y1 fxy1 ... xn yn fxyn).
% This clause can then e.g. be added to the database using coq.elpi.accumulate.
pred mk-lift-mapping
  i:term, % M
  i:term, % MTy
  o:prop. % The clause.
mk-lift-mapping M MTy (pi as_ bs fabs\ Clause as_ bs fabs) :-
  std.assert-ok! (coq.typecheck M MTy) "Invalid type.",
  pi as_ bs fabs\ mk-lift-mapping.loop M MTy as_ bs fabs [] [] [] (Clause as_ bs fabs).

pred mk-lift-mapping.loop 
  i:term, % M
  i:term, % MTy
  i:list term, i:list term, i:list term, % as, bs, fabs
  i:list term, i:list term, i:list term, % [xi, ..., x1] [yi, ..., y1] [fxyi, ..., fxy1]
  o:prop. % The resulting clause.
mk-lift-mapping.loop
  M {{ forall (Xi Yi : Type), (Xi -> Yi) -> lp:(MTy Xi Yi) }}  
  As Bs FABs
  Xs Ys FXYs
  (pi xi yi fxyi\ lift-mapping As Bs FABs xi yi fxyi => Clause xi yi fxyi)
:-
  !,
  %coq.say "loop",
  %coq.say "M=" M "MTy=" MTy,
  %coq.say "As=" As "Bs=" Bs "FABs=" FABs,
  %coq.say "Xs=" Xs "Ys=" Ys "FXYs=" FXYs, 
  pi xi yi fxyi\ 
    mk-lift-mapping.loop 
      { coq.mk-app M [xi, yi, fxyi] } (MTy xi yi) 
      As Bs FABs  
      [xi|Xs] [yi|Ys] [fxyi|FXYs]
      (Clause xi yi fxyi).

% Remember that Xs, Ys and FXYs are in reversed order. This doesn't matter for us here.
mk-lift-mapping.loop M {{ lp:T -> lp:U }} As Bs FABs Xs Ys FXYs (lift-mapping As Bs FABs T U M) :-
  % Check T does not contain any Yi.
  std.forall Ys (y\ not (occurs y T)),
  % Check U is equal to T with each Xi replaced by Yi.
  copy-with Xs Ys T U.

}}. 
Elpi Typecheck.

(* Command to extend the map database. *)
Elpi Command AddMap.
Elpi Accumulate Db map.db.
Elpi Accumulate lp:{{
main [trm M] :-
  std.assert-ok! (coq.typecheck M Mty) "Provided function does not typecheck",
  std.assert! (mk-lift-mapping M Mty Rule) "Provided function is not a mapping function",
  coq.say "Added rule:" Rule,
  coq.elpi.accumulate _ "map.db" (clause _ _ Rule).

main _ :- coq.error "This command expects a single term as input.".
}}.
Elpi Typecheck.
(*Elpi AddMap (prod_map).*)

Elpi Command DeriveMap.
Elpi Accumulate Db map.db.
Elpi Accumulate lp:{{
% Command entry point.  
main [str IndName] :- std.do! [
  % Locate the inductive type.
  std.assert! (coq.locate IndName (indt Ind)) "Could not find inductive type! Aborting.",
  % Check the inductive parameters have the required form.
  std.assert! (ind-params {coq.env.indt-decl Ind} PTys) "Inductive has dependent parameters! Aborting.",
  std.assert! (std.forall PTys (ty\ ty = sort _)) "The inductive parameters should have type [sort _] ! Aborting.",
  std.assert! (not (PTys = [])) "Inductive has no parameter! Aborting.",
  % Build the map function.
  build-map Ind PTys F,
  coq.say { coq.term->string F },
  std.assert-ok! (coq.typecheck F _) "Resulting function does not typecheck! Aborting.",
  % Add the function to the Coq global environment.
  Name is IndName ^ "_map",
  coq.ensure-fresh-global-id Name FName,
  coq.env.add-const FName F _ @transparent! C,
  coq.say "Added function under name" C
  % Set implicit arguments for the function.
  % For some reason we can't do this while building the function.
  %coq.arguments.set-implicit (const C) [[ maximal, maximal, explicit, explicit ]]
].

% ---------------------------------------------------------------------------------------

% [ind-params ind params] computes the type of each parameter 
% (uniform ones followed by non-uniform ones) of the inductive declaration [ind].
% This assumes the parameters are non-dependent (i.e. the type of each parameter is a closed term),
% otherwise it fails (softly).
pred ind-params i:indt-decl, o:list term.

% First gather the uniform parameters.
ind-params (parameter _ _ PTy Ind) [PTy|Rest] :-
  % Notice we do not allow Rest to depend on x.
  pi x\ ind-params (Ind x) Rest.
ind-params (inductive _ _ Arity _) Rest :- 
  ind-params.arity Arity Rest.

% Then the non-uniform parameters (which are stored in the inductive's arity).
ind-params.arity (parameter _ _ PTy Arity) [PTy|Rest] :-
  % Notice we do not allow Rest to depend on x.
  pi x\ ind-params.arity (Arity x) Rest.
ind-params.arity (arity _) [] :- !.

% ---------------------------------------------------------------------------------------

% Build the map function for a given inductive.
pred build-map 
  i:inductive,  % The inductive type (with parameters).
  i:list term,  % The types of the inductive parameters.
  o:term.       % The map function we are building.

% The fixpoint part. We use the argument [map] of the fixpoint to recursively map over subterms of [x] 
% which are of type [I As]. Technically this amounts to adding a (local) clause to lift-mapping.  
build-map I Ps (fix `map` N MapTy map\ F map) :-
  % The index of the structurally recursive argument (starting at 0).
  N is 3 * { std.length Ps },
  % The type of the recursive map function.
  build-map.ty I Ps [] [] MapTy,
  coq.say "map type :" { coq.term->string MapTy },
  @pi-decl `map` MapTy map\ 
    mk-lift-mapping map MapTy (Rule map), 
    coq.say "Recursive rule:" Rule,
    Rule map => 
    build-map.loop I Ps [] [] [] (F map).

% Build the type of the mapping function.
build-map.ty I [P|Ps] As Bs {{ forall (A B : lp:P), (A -> B) -> lp:(Ty A B) }} :-
  pi a b\ build-map.ty I Ps [a|As] [b|Bs] (Ty a b).
build-map.ty I [] As Bs {{ lp:IA -> lp:IB }} :-
  coq.mk-app (global (indt I)) { std.rev As } IA,
  coq.mk-app (global (indt I)) { std.rev Bs } IB.

pred build-map.loop
  i:inductive,  % The inductive type (with parameters).
  i:list term,  % The types of the inductive parameters.
  i:list term,  % Accumulator for the types As we map from (in reversed order). 
  i:list term,  % Accumulator for the types Bs we map to (in reversed order).
  i:list term,  % Accumulator for the functions Fs : As -> Bs.
  o:term.       % The map function we are building.

build-map.loop I [P|Ps] As Bs Fs {{ fun (A B : lp:P) (f : A -> B) => lp:(Body A B f) }} :- std.do! [
  @pi-decl `a` P a\ 
  @pi-decl `b` P b\ 
  @pi-decl `f` {{ lp:a -> lp:b }} f\
    build-map.loop I Ps [a|As] [b|Bs] [f|Fs] (Body a b f)
].

build-map.loop I [] As Bs Fs (fun `x` IA x\ Match x) :- std.do! [
  std.rev As RAs,
  std.rev Bs RBs,
  std.rev Fs RFs,
  coq.mk-app (global (indt I)) RAs IA,
  coq.mk-app (global (indt I)) RBs IB,
  @pi-decl `x` IA x\
    coq.build-match 
      x
      IA
      (_\_\_\r\ r = IB)
      (build-branch I RAs RBs RFs)
      (Match x)
].

% ---------------------------------------------------------------------------------------

pred build-branch 
  i:inductive, % I the inductive type.
  i:list term, % As the types of the parameters we map *from*.
  i:list term, % Bs the types of the parameters we map *to*.
  i:list term, % fs : As -> Bs the mapping functions.
  i:term, % The branch constructor (applied to the parameters).
  i:term, % The return type of the constructor.
  i:list term, % The arguments of the constructor (without the parameters).
  i:list term, % The types of each argument.
  o:term. % The resulting branch.

build-branch I As Bs Fs CA _ Args ArgsTy Branch :- std.do! [
  % Decide for each arg whether we leave it as is, apply a F or Map to it or if it can't be handled.
  std.map2 Args ArgsTy (build-branch.aux As Bs Fs) MappedArgs, 
  % Change the As with the Bs in the constructor.
  copy-with As Bs CA CB,
  % Apply the constructor to the new arguments.
  coq.mk-app CB MappedArgs Branch
].

build-branch.aux As Bs Fs Arg ArgTy NewArg :-
  copy-with As Bs ArgTy NewArgTy,
  %coq.say "As =" As, 
  %coq.say "Bs =" Bs,
  %coq.say "Fs =" Fs,
  %coq.say "ArgTy =" ArgTy,
  %coq.say "NewArgTy =" NewArgTy,
  lift-mapping As Bs Fs ArgTy NewArgTy FArg, 
  !, 
  coq.mk-app FArg [Arg] NewArg.

build-branch.aux A B F Arg ArgTy NewArg :- 
  coq.error "Can't map over argument of type [" { coq.term->string ArgTy } "]".

% ---------------------------------------------------------------------------------------

}}.

Elpi Typecheck.

(**************************************************************************)
(* Testing. *)


Elpi DeriveMap list.
Elpi AddMap (@list_map).
(*Elpi DeriveMap prod.
Elpi AddMap (@prod_map).*)

Inductive multi A B :=
  | Multi1 : A -> B -> A -> multi A B
  | Multi2 : bool -> list B -> nat -> multi A B.

Elpi DeriveMap multi.

Inductive double A := 
  | Double : A -> A -> double A.
Inductive tree A := 
  | Leaf : A -> bool -> tree A
  | Node : list (tree A) -> tree (list A) -> tree A.
Inductive weird A :=
  | Wunit : A -> weird A
  | Wlist : list (weird (double A)) -> weird A.


Elpi AddMap (@double_map).
Elpi AddMap (@List.map).
Elpi DeriveMap tree.
Elpi DeriveMap weird.

Print double_map.
Print tree_map.
Print weird_map.
