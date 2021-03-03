module Delude.List where

open import Agda.Primitive
open import Delude.Option
open import Delude.Functor

data List {a : Level} (A : Set a) : Set a where
  _∷_ : A → List A → List A
  [] : List A

instance FunctorList : {a : Level} → Functor {a} List

map ⦃ FunctorList ⦄ f (x ∷ xs) = f x ∷ map f xs
map ⦃ FunctorList ⦄ _ [] = []
