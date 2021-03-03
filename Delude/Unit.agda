module Delude.Unit where

open import Agda.Primitive

data ⊤ {a} : Set a where
  unit : ⊤ {a}
