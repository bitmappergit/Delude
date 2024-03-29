module Delude.Bimap where

open import Agda.Primitive

record Bimap {a b} (P : Set a → Set b → Set (a ⊔ b)) : Set (lsuc (a ⊔ b)) where
  field bimap : {A B : Set a} {C D : Set b} → (A → B) → (C → D) → P A C → P B D

open Bimap ⦃ ... ⦄ public
