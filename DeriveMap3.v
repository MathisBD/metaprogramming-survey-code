(**************************************************************************)
(* This version deals with multiple parameters. *)
(**************************************************************************)

From elpi Require Import elpi.

(* We store all the mapping functions found so far in a database,
   which we can extend at will (for instance when deriving a mapping function for
   an inductive, we can add it to the database). *)
Elpi Db map.db lp:{{

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

%lift-mapping A B FAB {{ list lp:T }} {{ list lp:U }} {{ @List.map lp:T lp:U lp:FTU }} :- 
%  lift-mapping A B FAB T U FTU.

% ----------------------------------------------------------

% Helper function to add a clause to lift-mapping. 
% It takes as input a term [M] and its type of the form [forall (A B : Type), (A -> B) -> T -> U] 
% where T does not contain B, and U is equal to T with A replaced by B. 
% It returns a lift-mapping clause that tells how to lift a function A -> B to a function T -> U. 
% This clause can then e.g. be added to the database using coq.elpi.accumulate.
%pred mk-lift-mapping i:term, i:term, o:prop.
%mk-lift-mapping M 
%  ({{ forall (A B : Type), (A -> B) -> lp:(T A B) -> lp:(U A B) }} as MTy)
%  (pi a b fab x y fxy\ lift-mapping a b fab (T x y) (U x y) {{ lp:M lp:x lp:y lp:fxy }} :- lift-mapping a b fab x y fxy) 
%:-
%  std.assert-ok! (coq.typecheck M MTy) "Invalid type.",
%  pi a b\
%  % Check T does not contain b.
%  not (occurs b (T a b)),
%  % Check U is equal to T with a replaced by b.
%  (copy a b => copy (T a b) (U a b)).
}}. 
Elpi Typecheck.

(* Command to extend the map database. *)
(*Elpi Command AddMap.
Elpi Accumulate Db map.db.
Elpi Accumulate lp:{{
main [trm M] :-
  std.assert-ok! (coq.typecheck M Mty) "Provided function does not typecheck",
  std.assert! (mk-lift-mapping M Mty Rule) "Provided function is not a mapping function",
  coq.elpi.accumulate _ "map.db" (clause _ _ Rule).
}}.
Elpi Typecheck.*)

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
  build-map Ind PTys [] [] [] F,
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
  i:list term,  % Accumulator for the types As we map from (in reversed order). 
  i:list term,  % Accumulator for the types Bs we map to (in reversed order).
  i:list term,  % Accumulator for the functions Fs : As -> Bs.
  o:term.       % The map function we are building.

build-map I [P|Ps] As Bs Fs {{ fun (A B : lp:P) (f : A -> B) => lp:(Body A B f) }} :- std.do! [
  @pi-decl `a` P a\ 
  @pi-decl `b` P b\ 
  @pi-decl `f` {{ lp:a -> lp:b }} f\
    build-map I Ps [a|As] [b|Bs] [f|Fs] (Body a b f)
].

build-map I [] As Bs Fs (fun `x` IA x\ Match x) :- std.do! [
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
      (build-branch I _ RAs RBs RFs)
      (Match x)
].

% ---------------------------------------------------------------------------------------

pred build-branch 
  i:inductive, % I the inductive type.
  i:term, % The recursive map function.
  i:list term, % As the types of the parameters we map *from*.
  i:list term, % Bs the types of the parameters we map *to*.
  i:list term, % fs : As -> Bs the mapping functions.
  i:term, % The branch constructor (applied to the parameters).
  i:term, % The return type of the constructor.
  i:list term, % The arguments of the constructor (without the parameters).
  i:list term, % The types of each argument.
  o:term. % The resulting branch.

build-branch I Map As Bs Fs CA _ Args ArgsTy Branch :- std.do! [
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

% For some reason I can't write this simply as [std.forall As Bs copy => copy T U].
pred copy-with i:list term, i:list term, i:term, o:term.
copy-with [] [] T U :- copy T U.
copy-with [A|As] [B|Bs] T U :- copy A B => copy-with As Bs T U.

}}.



(*
%(fix `map` XPos MapTy map\ (Body map)) %(A B : lp:PTy) (f : A -> B) (x : lp:GI A) {struct x} : lp:GI B := lp:(Match map A B f x) }} 
% :- std.do! [
%  GI = global (indt I),
%  % The position of the structurally recursive argument [x].
%  %XPos is 3 * { std.length PTy },
%  % The type of the recursive mapping function.
%  %MapTy = _, %{{ forall (A B : lp:PTy), (A -> B) -> lp:GI A -> lp:GI B }},
%  % The fixpoint part. We use the argument [map] to recursively map over subterms of [x] 
%  % which are of type [I A]. Technically this amounts to adding a (local) clause to lift-mapping.
%  %@pi-decl `map` MapTy map\ %mk-lift-mapping map MapTy (Rule map), Rule map =>
%  
%  Res = (
%    @funs `a` PTys as\ 
%    @funs PTys bs\ 
%    @funs `f` { std.map2 as bs (a\ b\ r\ r = prod _ a _\ b) } fs\ 
%    fun `x` { coq.mk-app GI as } x\
%      Match as bs fs x
%  ),
%
%  @pi-decls `a` PTys as\
%  @pi-decls `b` PTys bs\
%  @pi-decls `f` { std.map2 as bs (a\ b\ r\ r = prod _ a _\ b) } fs\
%  @pi-decl `x` { coq.mk-app GI as } x\
%    build-match I _ as bs fs x (Match as bs fs x)
%].
%  
%  % Bind the remaining arguments.
%  @pi-decl `a` PTy a\ 
%  @pi-decl `b` PTy b\ 
%  @pi-decl `f` {{ lp:a -> lp:b }} f\
%  @pi-decl `x` {{ lp:GI lp:a }} x\
%    % Build the inner match.
%    build-match I map a b f x (Match map a b f x)
%]. *)




Elpi Typecheck.

(**************************************************************************)
(* Testing. *)


Elpi DeriveMap prod.

Inductive multi A B :=
  | Multi1 : A -> B -> A -> multi A B
  | Multi2 : bool -> B -> nat -> multi A B.

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
