module Delude.Semiring where

open import Agda.Primitive

record Semiring {a} (A : Set a) : Set a where
  infixl 6 _+_
  infixl 7 _*_

  field zro one : A
  field _+_ _*_ : A -> A -> A

  {-# INLINE zro #-}
  {-# INLINE one #-}

open Semiring ⦃ ... ⦄ public
