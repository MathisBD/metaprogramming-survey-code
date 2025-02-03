module Test where

open import Agda.Primitive using (Setω)
open import Data.Bool
open import Data.Maybe
open import Data.List
open import Data.Product
open import Function.Base
open import Class.Functor

instance 
  functor-id : Functor (\{l} (T : Set l) -> T)
  functor-id = record { _<$>_ = \f x -> f x }
{-# INCOHERENT functor-id #-}

instance 
  functor-comp : {F G : ∀ {l} -> Set l -> Set l} -> {{Functor F}} -> {{Functor G}} -> Functor (\{l} T -> G (F T))
  functor-comp {F} {G} {{hF}} {{hG}} = record { _<$>_ = \f x -> fmap {G} {{hG}} (fmap {F} {{hF}} f) x }
{-# OVERLAPPABLE functor-comp #-}

itω : {A : Setω} → {{A}} → A
itω {{x}} = x

_ : Functor (\{l} T -> Maybe (List (Maybe T)))
_ = itω