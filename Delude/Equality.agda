module Delude.Equality where

open import Agda.Primitive

infix 4 _≡_

data _≡_ {a : Level} {A : Set a} (x : A) : A → Set a where
  instance refl : x ≡ x
