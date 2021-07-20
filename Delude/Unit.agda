module Delude.Unit where

open import Agda.Primitive

record ⊤ : Set where
  instance constructor unit

{-# BUILTIN UNIT ⊤ #-}
{-# COMPILE GHC ⊤ = data () (()) #-}
