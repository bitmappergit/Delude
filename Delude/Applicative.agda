module Delude.Applicative where

open import Agda.Primitive

open import Delude.Functor

private
  variable
    a b : Level

record Applicative (F : Set a → Set b) : Set (lsuc (a ⊔ b)) where
  infixl 4 _<*>_
  
  field pure : {A : Set a} → A → F A
  field _<*>_ : {A B : Set a} → F (A → B) → F A → F B
  field ⦃ super ⦄ : Functor F

open Applicative ⦃ ... ⦄ public
