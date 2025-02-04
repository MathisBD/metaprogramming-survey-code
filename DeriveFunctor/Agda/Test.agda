module Test where

open import Agda.Primitive using (Setω)
open import Data.Bool
open import Data.Maybe
open import Data.List
open import Data.Product
open import Function.Base
open import Class.Functor
open import Agda.Builtin.Reflection

data Tree {l} (A : Set l) : Set l where
  leaf : Tree A
--  node : Tree A -> A -> Tree A -> Tree A
--
--fmap-tree : ∀ {a b} -> {A : Set a} -> {B : Set b} -> (A -> B) -> Tree A -> Tree B
--fmap-tree f leaf = leaf
--fmap-tree f (node l x r) = 
--  let rec-inst : Functor Tree
--      rec-inst = record { _<$>_ = fmap-tree }
--  in   
--  node (fmap f l) (f x) (fmap f r)


