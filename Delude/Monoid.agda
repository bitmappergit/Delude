module Delude.Monoid where

open import Delude.Semigroup

record Monoid {a} (A : Set a) : Set a where
  field empty : A
  field ⦃ super ⦄ : Semigroup A

open Monoid ⦃ ... ⦄ public
