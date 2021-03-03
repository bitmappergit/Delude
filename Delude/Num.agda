module Delude.Num where

open import Agda.Primitive

open import Delude.Function
open import Delude.Nat

record Num {a : Level} (A : Set a) : Set a where
  field
    fromNat : ℕ → A
    toNat : A → ℕ

  {-# INLINE fromNat #-}
  {-# INLINE toNat #-}

open Num ⦃ ... ⦄ public

{-# BUILTIN FROMNAT fromNat #-}

instance NumNat : Num ℕ

fromNat ⦃ NumNat ⦄ = id
toNat ⦃ NumNat ⦄ = id
