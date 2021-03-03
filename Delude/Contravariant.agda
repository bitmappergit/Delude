module Delude.Contravariant where

open import Agda.Primitive

record Contravariant {a b : Level} (F : Set a → Set b) : Set (lsuc a ⊔ b) where
  field contramap : {A B : Set a} → F A → F B

open Contravariant ⦃ ... ⦄ public 
