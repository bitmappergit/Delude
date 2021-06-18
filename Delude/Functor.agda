module Delude.Functor where

open import Agda.Primitive

private
  variable
    a b : Level

record Functor (F : Set a → Set b) : Set (lsuc (a ⊔ b)) where
  field map : {A B : Set a} → (A → B) → F A → F B

  _<$>_ : {A B : Set a} → (A → B) → F A → F B
  _<$>_ = map

  infixl 4 _<$>_

open Functor ⦃ ... ⦄ public
