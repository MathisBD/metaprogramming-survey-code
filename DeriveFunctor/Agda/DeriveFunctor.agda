module DeriveFunctor where

open import Data.Nat
open import Data.Maybe
open import Data.List

fmap : (A B : Set) -> (A -> B) -> Maybe A -> Maybe B
fmap A B f nothing = nothing
fmap A B f (just x) = just (f x)




