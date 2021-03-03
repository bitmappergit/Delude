module Delude.Neg where

open import Agda.Primitive

open import Delude.Semiring
open import Delude.Ring
open import Delude.Num
open import Delude.Nat

record Neg {a} (A : Set a) ⦃ _ : Semiring A ⦄ ⦃ _ : Ring A ⦄ ⦃ _ : Num A ⦄ : Set a where
  field fromNeg : ℕ → A

open Neg ⦃ ... ⦄ public

{-# BUILTIN FROMNEG fromNeg #-}
