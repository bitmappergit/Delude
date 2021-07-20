module Delude.Product where

open import Agda.Primitive

open import Delude.Function

record Σ {a b : Level} (A : Set a) (B : A → Set b) : Set (a ⊔ b) where
  constructor _,_
  field
    fst : A
    snd : B fst

open Σ public

infixr 4 _,_

_×_ : {a b : Level} → Set a → Set b → Set (a ⊔ b)
_×_ A B = Σ A (λ _ → B)
