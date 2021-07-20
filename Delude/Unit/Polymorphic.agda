module Delude.Unit.Polymorphic where

open import Agda.Primitive

record ⊤ {a} : Set a where
  instance constructor unit
