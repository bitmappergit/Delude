module Delude.Function where

open import Agda.Primitive

infixr 9 _$_
infixr 9 _∘_
infixl 1 _&_

id : ∀ {a} {A : Set a} → A → A
id x = x

{-# INLINE id #-}

const : ∀ {a b} {A : Set a} {B : Set b} → A → B → A
const x _ = x

{-# INLINE const #-}

_$_ : ∀ {a b} {A : Set a} {B : A → Set b}
    → ((x : A) → B x)
    → (x : A)
    → B x
_$_ f x = f x

{-# INLINE _$_ #-}

_&_ : ∀ {a b} {A : Set a} {B : A → Set b}
    → (x : A)
    → ((x : A) → B x)
    → B x
_&_ x f = f x

{-# INLINE _&_ #-}

_∘_ : ∀ {a b c} {A : Set a} {B : A → Set b} {C : (x : A) → B x → Set c}
    → (f : {x : A} (y : B x) → C x y)
    → (g : (x : A) → B x)
    → ((x : A) → C x (g x))
_∘_ f g = λ x → f (g x)

{-# INLINE _∘_ #-}


flip : ∀ {a b c} {A : Set a} {B : Set b} {C : A → B → Set c}
     → ((x : A) (y : B) → C x y)
     → ((y : B) (x : A) → C x y)
flip f = λ y x → f x y

{-# INLINE flip #-}

case_of_ : ∀ {a b} {A : Set a} {B : A → Set b}
         → (x : A)
         → ((x : A) → B x)
         → B x
case_of_ = _&_

infix 0 case_of_

{-# INLINE case_of_ #-}
