module Delude.Empty where

open import Agda.Primitive

data ⊥ : Set where

⊥-elim : {a : Level} → {A : Set a} → ⊥ → A
⊥-elim ()
