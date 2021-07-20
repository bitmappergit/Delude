module Delude.Unit.Polymorphic where

open import Agda.Primitive

data ⊤ {a} : Set a where
  unit : ⊤ {a}
