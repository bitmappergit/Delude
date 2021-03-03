module Delude.Eq where

open import Agda.Primitive

open import Delude.Bool

record Eq {a : Level} (A : Set a) : Set a where
  field
    _==_ : A → A → Bool
  
  _!=_ : A → A → Bool
  x != y = ¬ (x == y)

open Eq ⦃ ... ⦄ public

instance EqBool : Eq Bool

_==_ ⦃ EqBool ⦄ #t #t = #t
_==_ ⦃ EqBool ⦄ #f #f = #t
_==_ ⦃ EqBool ⦄ #f #t = #f
_==_ ⦃ EqBool ⦄ #t #f = #f
