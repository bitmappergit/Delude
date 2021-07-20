module Delude.Vec where

open import Agda.Primitive

open import Delude.Nat
open import Delude.Functor
open import Delude.Semiring
open import Delude.Function
open import Delude.Semigroup
open import Delude.Monoid

infixr 5 _∷_ _++_

data Vec {a} (A : Set a) : ℕ → Set a where
  _∷_ : {s : ℕ} → A → Vec A s → Vec A (suc s)
  [] : Vec A 0

replicate : ∀ {a s} {A : Set a} → A → Vec A s
replicate {s = suc x} val = val ∷ replicate {s = x} val
replicate {s = zero} val = []

instance FunctorVec : ∀ {a s} → Functor {a} (λ A → Vec A s)

map ⦃ FunctorVec ⦄ f (x ∷ xs) = f x ∷ map f xs
map ⦃ FunctorVec ⦄ _ [] = []

drop : ∀ {a s} {A : Set a} → (t : ℕ) → Vec A (t + s) → Vec A s
drop (suc t) (_ ∷ xs) = drop t xs
drop zero result = result

take : ∀ {a s} {A : Set a} → (t : ℕ) → Vec A (t + s) → Vec A t
take (suc t) (x ∷ xs) = x ∷ take t xs
take zero _ = []

_++_ : ∀ {a m n} {A : Set a} → Vec A m → Vec A n → Vec A (m + n)
_++_ [] ys = ys
_++_ (x ∷ xs) ys = x ∷ xs ++ ys
