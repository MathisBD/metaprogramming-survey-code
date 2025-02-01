module Test where

open import Data.Unit
open import Data.Bool
open import Data.Maybe hiding (_>>=_)
open import Data.List
open import Data.Nat
open import Function.Base
open import Agda.Builtin.Sigma
open import Agda.Builtin.Reflection
open import Reflection
open import Agda.Primitive

macro
  test : Term -> TC ⊤
  test hole =
    inContext (("A" , vArg (agda-sort $ Sort.set $ var 0 [])) ∷ ("a" , vArg (quoteTerm Level)) ∷ []) do
      let t : Term
          t = con (quote just) (hArg (var 1 []) ∷ hArg (var 0 []) ∷ [])
      --inferType t
      unify hole (quoteTerm tt)
    