module Delude.Product where

open import Agda.Primitive

open import Delude.Function

private
  variable
    a b : Level

record Σ (A : Set a) (B : A → Set b) : Set (a ⊔ b) where
  constructor _,_
  field
    fst : A
    snd : B fst

open Σ public

infixr 4 _,_

_×_ : Set a → Set b → Set (a ⊔ b)
_×_ A B = Σ A (λ _ → B)
