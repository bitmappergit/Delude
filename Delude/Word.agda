module Delude.Word where

open import Agda.Primitive

open import Delude.Vec
open import Delude.Bool
open import Delude.Function
open import Delude.Functor
open import Delude.Num
open import Delude.Nat
open import Delude.Semiring
open import Delude.Ring
open import Delude.Divisible
open import Delude.Neg
open import Delude.Eq
open import Delude.Ord

Word : ℕ → Set
Word = Vec Bool

word-add : {s : ℕ} → Bool → Word s → Word s → Word s
word-add c (#t ∷ m) (#t ∷ n) = c ∷ word-add #t m n
word-add c (#f ∷ m) (#f ∷ n) = c ∷ word-add #f m n
word-add c (#t ∷ m) (#f ∷ n) = not c ∷ word-add c m n
word-add c (#f ∷ m) (#t ∷ n) = not c ∷ word-add c m n
word-add _ [] [] = []

{-# INLINE word-add #-}

instance SemiringWord : {s : ℕ} → Semiring (Word s)
instance RingWord : {s : ℕ} → Ring (Word s)
instance NumWord : {s : ℕ} → Num (Word s)
instance NegWord : {s : ℕ} → Neg (Word s)

zro ⦃ SemiringWord ⦄ = replicate #f
one ⦃ SemiringWord {zero} ⦄ = []
one ⦃ SemiringWord {suc _} ⦄ = #t ∷ zro
_+_ ⦃ SemiringWord ⦄ = word-add #f
_*_ ⦃ SemiringWord ⦄ a = mul a ∘ toNat
  where mul : {s : ℕ} → Word s → ℕ → Word s
        mul m (suc n) = word-add #f m (mul m n)
        mul m zero = zro

negate ⦃ RingWord ⦄ x = word-add #t zro (map not x)
_-_ ⦃ RingWord ⦄ a b = word-add #t a (map not b)

fromNat ⦃ NumWord {zero} ⦄ _ = []
fromNat ⦃ NumWord {suc _} ⦄ zero = zro
fromNat ⦃ NumWord {suc _} ⦄ (suc x) with (suc x % suc one)
... | zero = #f ∷ fromNat (suc x / suc one)
... | suc _ = #t ∷ fromNat (suc x / suc one)

toNat ⦃ NumWord ⦄ = toNat′ one
  where toNat′ : {s : ℕ} → ℕ → Word s → ℕ
        toNat′ c (#t ∷ xs) = c + toNat′ (c * suc one) xs
        toNat′ c (#f ∷ xs) = toNat′ (c * suc one) xs
        toNat′ c [] = zro

fromNeg ⦃ NegWord ⦄ = negate ∘ fromNat

Word4 = Word 4
Word8 = Word 8
Word16 = Word 16
Word32 = Word 32
Word64 = Word 64

instance EqWord : {s : ℕ} → Eq (Word s)

_==_ ⦃ EqWord ⦄ (x ∷ xs) (y ∷ ys) = (x == y) ∧ (xs == ys)
_==_ ⦃ EqWord ⦄ [] [] = #t

instance OrdWord : {s : ℕ} → Ord (Word s)

_<_ ⦃ OrdWord ⦄ (#t ∷ xs) (#t ∷ ys) = xs < ys
_<_ ⦃ OrdWord ⦄ (#f ∷ xs) (#f ∷ ys) = xs < ys
_<_ ⦃ OrdWord ⦄ (#t ∷ xs) (#f ∷ ys) = #f
_<_ ⦃ OrdWord ⦄ (#f ∷ xs) (#t ∷ ys) = #t
_<_ ⦃ OrdWord ⦄ [] [] = #f

_>_ ⦃ OrdWord ⦄ (#t ∷ xs) (#t ∷ ys) = xs > ys
_>_ ⦃ OrdWord ⦄ (#f ∷ xs) (#f ∷ ys) = xs > ys
_>_ ⦃ OrdWord ⦄ (#t ∷ xs) (#f ∷ ys) = #t
_>_ ⦃ OrdWord ⦄ (#f ∷ xs) (#t ∷ ys) = #f
_>_ ⦃ OrdWord ⦄ [] [] = #f
