From DeriveFunctor.Functor Require Import Functor.
From elpi Require Import elpi.

Elpi Command DeriveFunctor.
Elpi Accumulate lp:{{

% Command entry point.  
main [str IndName] :- std.do! [
  % Locate the inductive type.
  std.assert! (coq.locate IndName (indt Ind)) "Could not find inductive type.",
  % Check the inductive has exactly one uniform parameter.
  (coq.env.indt-decl Ind (parameter _ _ ParamTy _\ inductive _ tt _ _)
  ; coq.error "This command only supports inductive types with exactly one uniform parameter."),
  % Check the parameter is a type.
  std.assert! (ParamTy = sort _) "The inductive parameter's type should be Type.",
  % Build the functor instance.
  build-fmap Ind ParamTy FuncRaw,
  InstRaw = {{ Build_Functor _ lp:FuncRaw }},
  std.assert-ok! (coq.typecheck InstRaw InstTy) "Resulting instance does not typecheck.",
  % Infer typeclass arguments.
  std.assert-ok! (coq.elaborate-skeleton InstRaw InstTy Inst) "Failed to elaborate typeclass arguments",
  % Normalize the instance. 
  coq.reduction.cbv.norm Inst InstRed,
  % Declare the Functor instance we just built.
  coq.ensure-fresh-global-id { calc (IndName ^ "_functor") } InstName,
  coq.env.add-const InstName InstRed InstTy @transparent! C,
  coq.TC.declare-instance (const C) 0
].

% ---------------------------------------------------------------------------------------

pred build-fmap 
  i:inductive,  % The inductive type (with parameters).
  i:term,       % The type of the inductive parameter.
  o:term.       % The map function we are building.

% Build the fmap function.
build-fmap I PTy 
  {{ fix map (A B : lp:PTy) (f : A -> B) (x : lp:(FI A)) {struct x} : lp:(FI B) := 
       let _ := Build_Functor _ map in
       lp:(Match map A B f x) }} 
:- std.do! [
  (pi x\ coq.mk-app { coq.env.global (indt I) } [x] (FI x)),
  % Bind the parameters.
  @pi-decl `map` _ map\ 
  @pi-decl `A` PTy a\
  @pi-decl `B` PTy b\
  @pi-decl `f` {{ lp:a -> lp:b }} f\
  @pi-decl `x` (FI a) x\
  % Bind the recursive instance.
  @pi-def `rec_inst` _ _ _\
    % Build the inner match.
    coq.build-match 
      x
      (FI a)
      (_\_\_\r\ r = FI b)
      (build-branch I a b f)
      (Match map a b f x)
]. 

% ---------------------------------------------------------------------------------------

pred build-branch 
  i:inductive, % I the inductive type.
  i:term, % A the value of the parameter we map *from*.
  i:term, % B the value of the parameter we map *to*.
  i:term, % f : A -> B the mapping function.
  i:term, % The branch constructor (applied to the parameters).
  i:term, % The return type of the constructor.
  i:list term, % The arguments of the constructor (without the parameters).
  i:list term, % The types of each arguments.
  o:term. % The resulting branch.

build-branch I A B F CA _ Args ArgsTy Branch :- std.do! [
  % Decide for each arg whether we leave it as is, apply F or Map to it or if it can't be handled.
  std.map2 Args ArgsTy (build-arg A B F) MappedArgs, 
  % Change A with B in the constructor.
  (copy A B => copy CA CB),
  % Apply the constructor to the new arguments.
  coq.mk-app CB MappedArgs Branch
].

pred build-arg i:term, i:term, i:term, i:term, i:term, o:term.

% If A does not occur in ArgTy, there is nothing to do.
build-arg A B F Arg ArgTy Arg :- not (occurs A ArgTy), !.
% Otherwise apply [fmap F] to the argument Arg.
build-arg A B F Arg ArgTy Res :-
  % Determine over which functor we are mapping.
  (pi x\ copy A x => FctorFun x = { copy ArgTy }),
  Fctor = fun `a` Aty FctorFun,
  % Apply fmap
  coq.mk-app {{ @Functor.fmap }} [ Fctor, Inst, A, B, F, Arg] Res.

}}.
Elpi Typecheck.

Elpi DeriveFunctor list.
Elpi DeriveFunctor option.
(*Instance : Functor list := { fmap := List.map }.
Instance : Functor option := { fmap := option_map }.*)

Inductive tree A :=
  | Leaf : A -> tree A
  | Node : bool -> list (option (tree A)) -> tree A.
Elpi DeriveFunctor tree.

Inductive tree2 A :=
  | T : list (tree (option A)) -> tree2 A.
Elpi DeriveFunctor tree2.
