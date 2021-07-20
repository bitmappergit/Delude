module Delude.Negation where

open import Agda.Primitive
open import Delude.Empty

infix 3 ¬_

¬_ : ∀ {a} → Set a → Set a
¬ p = p → ⊥

