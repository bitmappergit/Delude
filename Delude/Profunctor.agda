module Delude.Profunctor where

open import Agda.Primitive

open import Delude.Functor

record Profunctor {a b : Level} (P : Set a → Set b → Set (a ⊔ b)) : Set (lsuc (a ⊔ b)) where
  field dimap : {A B : Set a} {C D : Set b} → (A → B) → (C → D) → P B C → P A D

open Profunctor ⦃ ... ⦄ public
