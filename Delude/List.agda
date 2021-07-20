module Delude.List where

open import Agda.Primitive

open import Delude.Option
open import Delude.Functor
open import Delude.Semigroup
open import Delude.Monoid

data List {a} (A : Set a) : Set a where
  _∷_ : A → List A → List A
  [] : List A

instance FunctorList : ∀ {a} → Functor {a} List

map ⦃ FunctorList ⦄ f (x ∷ xs) = f x ∷ map f xs
map ⦃ FunctorList ⦄ _ [] = []

instance SemigroupList : ∀ {a} {A : Set a} → Semigroup (List A)

_∙_ ⦃ SemigroupList ⦄ [] ys = ys
_∙_ ⦃ SemigroupList ⦄ (x ∷ xs) ys = x ∷ (xs ∙ ys)

instance MonoidList : ∀ {a} {A : Set a} → Monoid (List A)

empty ⦃ MonoidList ⦄ = []
