module Delude.Nat where

open import Agda.Primitive

open import Delude.Function
open import Delude.Semiring
open import Delude.Divisible
open import Delude.Bool
open import Delude.Eq
open import Delude.Ord

data ℕ : Set where
  suc : ℕ → ℕ
  zero : ℕ

{-# BUILTIN NATURAL ℕ #-}

private
  natPlus : ℕ → ℕ → ℕ
  natPlus zero n = n
  natPlus (suc m) n = suc (natPlus m n)

  natTimes : ℕ → ℕ → ℕ
  natTimes zero _ = zero
  natTimes (suc m) n = natPlus n (natTimes m n)

instance SemiringNat : Semiring ℕ

zro ⦃ SemiringNat ⦄ = zero
one ⦃ SemiringNat ⦄ = suc zero
_+_ ⦃ SemiringNat ⦄ = natPlus
_*_ ⦃ SemiringNat ⦄ = natTimes 

{-# BUILTIN NATPLUS natPlus #-}
{-# BUILTIN NATTIMES natTimes #-}

_∸_ : ℕ → ℕ → ℕ
n     ∸ zero = n
zero  ∸ suc m = zero
suc n ∸ suc m = n ∸ m

infixl 6 _∸_

{-# BUILTIN NATMINUS _∸_ #-}

div-helper : (k m n j : ℕ) → ℕ
div-helper k m zero j = k
div-helper k m (suc n) zero = div-helper (suc k) m n m
div-helper k m (suc n) (suc j) = div-helper k m n j

{-# BUILTIN NATDIVSUCAUX div-helper #-}

mod-helper : (k m n j : ℕ) → ℕ
mod-helper k m zero j = k
mod-helper k m (suc n) zero = mod-helper zero m n m
mod-helper k m (suc n) (suc j) = mod-helper (suc k) m n j

{-# BUILTIN NATMODSUCAUX mod-helper #-}

instance DivisibleNat : Divisible ℕ

_/_ ⦃ DivisibleNat ⦄ n (suc m) = div-helper zero m n m
_/_ ⦃ DivisibleNat ⦄ _ zero = zero

_%_ ⦃ DivisibleNat ⦄ n (suc m) = mod-helper zero m n m
_%_ ⦃ DivisibleNat ⦄ _ zero = zero

instance EqNat : Eq ℕ

_==_ ⦃ EqNat ⦄ zero zero = #t
_==_ ⦃ EqNat ⦄ (suc x) (suc y) = x == y
_==_ ⦃ EqNat ⦄ (suc _) zero = #f
_==_ ⦃ EqNat ⦄ zero (suc _) = #f

instance OrdNat : Ord ℕ

_<_ ⦃ OrdNat ⦄ zero (suc _) = #t
_<_ ⦃ OrdNat ⦄ (suc _) zero = #f
_<_ ⦃ OrdNat ⦄ (suc x) (suc y) = x < y
_<_ ⦃ OrdNat ⦄ zero zero = #f

_>_ ⦃ OrdNat ⦄ zero (suc _) = #f
_>_ ⦃ OrdNat ⦄ (suc _) zero = #t
_>_ ⦃ OrdNat ⦄ (suc x) (suc y) = x > y
_>_ ⦃ OrdNat ⦄ zero zero = #f
