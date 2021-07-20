module Delude.Functor where

open import Agda.Primitive

record Functor {a b} (F : Set a → Set b) : Set (lsuc a ⊔ b) where
  field map : {A B : Set a} → (A → B) → F A → F B

  _<$>_ : {A B : Set a} → (A → B) → F A → F B
  _<$>_ = map

  infixl 4 _<$>_

open Functor ⦃ ... ⦄ public
