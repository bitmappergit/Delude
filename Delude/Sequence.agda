module Delude.Sequence where

open import Agda.Primitive

record Sequence {a : Level} (F : Set a → Set a) : Set (lsuc a) where
  field head : {A : Set a} → F A → A
  field tail : {A : Set a} → F A → F A

open Sequence ⦃ ... ⦄ public
