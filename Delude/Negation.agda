module Delude.Negation where

open import Agda.Primitive
open import Delude.Empty

infix 3 ¬_

¬_ : {a : Level} → Set a → Set a
¬ p = p → ⊥

