module Delude.Equality where

open import Agda.Primitive

open import Delude.Product
open import Delude.Negation

infix 4 _≡_

data _≡_ {a} {A : Set a} (x : A) : A → Set a where
  instance refl : x ≡ x

{-# BUILTIN EQUALITY _≡_ #-}

infix 4 _≢_

_≢_ : ∀ {a} {A : Set a} → (x y : A) → Set a
x ≢ y = ¬ (x ≡ y)

cong : ∀ {a} {A B : Set a} {x y : A}
     → (f : A → B)
     → x ≡ y
     ---------------
     → f x ≡ f y
cong f refl = refl

sym : ∀ {a} {A : Set a} {x y : A}
    → x ≡ y
    -------------
    → y ≡ x
sym refl = refl

trans : ∀ {a} {A : Set a} {x y z : A}
      → x ≡ y
      → y ≡ z
      -------------
      → x ≡ z
trans refl refl = refl


