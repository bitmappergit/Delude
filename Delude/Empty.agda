module Delude.Empty where

open import Agda.Primitive

data ⊥ : Set where

⊥-elim : ∀ {a} {A : Set a} → ⊥ → A
⊥-elim ()
