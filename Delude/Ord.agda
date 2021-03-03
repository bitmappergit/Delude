module Delude.Ord where

open import Agda.Primitive

open import Delude.Bool
open import Delude.Eq

private
  variable
    a : Level

record Ord (A : Set a) : Set a where
  field
    _<_ : A → A → Bool
    _>_ : A → A → Bool
    ⦃ EqA ⦄ : Eq A

  _≤_ : A → A → Bool
  x ≤ y = (x < y) ∨ (x == y)
  
  _≥_ : A → A → Bool
  x ≥ y = (x > y) ∨ (x == y)

open Ord ⦃ ... ⦄ public
