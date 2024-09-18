From elpi Require Import elpi.

(* [abstract ind_name term] abstracts out [term] from the inductive
   type [ind_name] and adds it as a parameter. *)
Elpi Command abstract.

Elpi Accumulate lp:{{

% Add a ' to an identifier.
pred prime i:id, o:id.
prime Id Id' :- Id' is Id ^ "'".

% Map functions over the fields of an inductive constuctor [indc-decl].
pred map-indc i:(id -> id -> prop), i:(arity -> arity -> prop), i:indc-decl, o:indc-decl.
map-indc FId FArity (constructor Id Arity) (constructor Id' Arity') :- 
  FId Id Id',
  FArity Arity Arity'.

% [abstract inductive term ty new-inductive].
% This is where the heavy lifting happens.
pred abstract i:indt-decl, i:term, i:term, o:indt-decl.
abstract Ind Term Ty Res :-
  % Destruct the inductive declaration.
  Ind = inductive Id Flag Arity Constructors,
  % Add a parameter to the inductive.
  Res = parameter "A" explicit Ty Res',
  % Abstract the parameter in the inductive.
  (pi a\ 
    (copy Term a :- !) => 
    (std.map (Constructors a) (map-indc prime copy-arity) (Constructors' a), 
    Res' a = inductive { prime Id } Flag { copy-arity Arity } Constructors')),
  % Check the new inductive is well-typed.
  coq.say "New inductive\n" Res,
  coq.assert-ok! (coq.typecheck-indt-decl Res) "Abstraction failed!".
  

main [str IndName, trm Param] :-
  % Fetch the inductive definition.
  std.assert! (coq.locate IndName (indt Ind)) "Not an inductive type!",
  % Elaborate the term to be abstracted.
  std.assert-ok! (coq.elaborate-skeleton Param Ty Term) "Ill-typed parameter!",
  % Create a new inductive definition.
  abstract { coq.env.indt-decl Ind } Term Ty NewInd,
  % Add the new inductive to the global environment.
  coq.env.add-indt NewInd _.
}}.

Elpi Typecheck.

Inductive tree :=
  | Leaf : option nat -> tree
  | Node : tree -> option nat -> tree -> tree.

(*Elpi abstract tree (option nat).*)

Inductive t (A : Type) (B : A * A) :=
  | Construct : A -> B -> t A B.


Check t.map : 
  forall A B, 
  forall A' B', 
  (A -> A') -> 
  (B -> B') -> 
  t A B -> t A' B'.