Declare ML Module "coq-metaprogramming.derivemap.plugin".


Inductive mylist A :=
  | mynil : mylist A
  | mycons : A -> mylist A -> mylist A.

(*TestCommand mydef.*)

DeriveMap mylist.