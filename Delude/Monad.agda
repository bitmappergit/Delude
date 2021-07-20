module Delude.Monad where

open import Agda.Primitive

open import Delude.Functor
open import Delude.Applicative

record Monad {a b} (M : Set a → Set b) : Set (lsuc (a ⊔ b)) where
  infixl 1 _>>=_ _>>_
  
  field _>>=_ : {A B : Set a} → M A → (A → M B) → M B
  field ⦃ super ⦄ : Applicative M
  
  return : {A : Set a} → A → M A
  return = pure

  _>>_ : {A B : Set a} → M A → M B → M B
  _>>_ a b = a >>= λ _ → b

open Monad ⦃ ... ⦄ public
