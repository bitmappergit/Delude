module Delude.Contravariant where

open import Agda.Primitive

private
  variable
    a b : Level

record Contravariant (F : Set a → Set b) : Set (lsuc (a ⊔ b)) where
  field contramap : {A B : Set a} → F A → F B

open Contravariant ⦃ ... ⦄ public 
