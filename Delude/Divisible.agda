module Delude.Divisible where

open import Agda.Primitive

record Divisible {a} (A : Set a) : Set a where
  field
    _/_ : A → A → A
    _%_ : A → A → A

open Divisible ⦃ ... ⦄ public
