module Delude.Ring where

open import Agda.Primitive

open import Delude.Semiring

record Ring {a : Level} (A : Set a) : Set a where
  infixl 6 _-_
  
  field _-_ : A → A → A
  field negate : A → A
  field ⦃ SemiringA ⦄ : Semiring A

open Ring ⦃ ... ⦄ hiding (SemiringA) public
