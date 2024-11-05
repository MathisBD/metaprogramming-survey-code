From DeriveMap.MetaCoq Require Import CommandDeBruijn.
From MetaCoq.Utils Require Import utils.
From MetaCoq.Template Require Import All.

Inductive double A := 
  | Dnil : bool -> double A
  | Double : option (option A) -> list (list (double A)) -> double A.

MetaCoq Run (derive_map "double").

Print double_map.