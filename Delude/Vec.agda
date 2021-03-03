module Delude.Vec where

open import Agda.Primitive

open import Delude.Nat
open import Delude.Functor

infixr 5 _∷_

data Vec {a : Level} (A : Set a) : ℕ → Set a where
  _∷_ : {s : ℕ} → A → Vec A s → Vec A (suc s)
  [] : Vec A 0

replicate : {s : ℕ} → ∀ {a} {A : Set a} → A → Vec A s
replicate {suc x} val = val ∷ replicate {x} val
replicate {zero} val = []

instance FunctorVec : ∀ {a s} → Functor {a} (λ A → Vec A s)

map ⦃ FunctorVec ⦄ f (x ∷ xs) = f x ∷ map f xs
map ⦃ FunctorVec ⦄ _ [] = []
