# Questions for the experts

1. Unification in the presence of universe polymorphism.
Example : recognize "mapping functions". In Lean syntax :
  List.map.{u1, u2} : forall (A : Type u1) (B : Type u2), (A -> B) -> List.{u1} A -> List.{u2} B
general pattern : 
  forall (A : Type u1) (B : Type u2), (A -> B) -> ?T A -> ?T B
problem : this does not unify (because it requires List.{u1} = List.{u2})
The nice way to solve this would be to allow metavariables to depend on universe levels : ?T.{u}

# Thoughts on derive-map 

Elpi : by far the best (HOAS + relational programming = both concise and easy to use).
Ltac2 : no support for open terms (e.g. can't typecheck or unify open terms) makes it a horrible mess.
Ocaml : a couple orthogonal issues
- the API is a mixture of low-level and high-level stuff -> I reimplemented a couple "obvious" functions which are probably already there somewhere
- threading state : the environment (local and global) and evar map (which contains the unification state + some universe stuff)
  Possible options :
  1. pass the env and evar_map to every function, and return the updated evar_map
  2. use a reader/state monad to make it nicer
  3. use a global env and evar_map -> probably a bad idea : even though Coq already has a global env, updating it is quite heavy and controlled
  Apparently 1. is the most common, and is what I went with in derive-map.
  Option 2. is what Lean does and is IMO nicer, except in Coq it might be awkward because Coq doesn't use a monadic interface.
- binder representation :
  1. locally nameless is very nice to use, but performance can suffer.
  2. pure de Bruijn is quite bad as expected.
  3. mixed de Bruijn (Weituo style) is nicer to use than pure de Bruijn.
     Is it really faster than pure de Bruijn ? When requesting a variable from the context it is sufficient to simply add an integer to the de Bruijn index,
     but when requesting the type of a variable one has to LIFT the entire type.
     EXAMPLE :
       You are working on a (dependent) telescope (x1 : T1) (x2 : T2) ... (xn : Tn)
       and you would like to map each term Ti into a term Ui(T1, ..., Ti) which can depend on the type of the previous variables
       At each step you have to instantiate the types T1 ... Ti at depth i, which means LIFTING them all. 
     
 
