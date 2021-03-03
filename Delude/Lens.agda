module Delude.Lens where

open import Agda.Primitive

open import Delude.Function
open import Delude.Functor
open import Delude.Identity
open import Delude.Const
open import Delude.Profunctor

infixr 4 _%~_
infixr 4 _:~_
infixr 4 _∙_

data Exchange {a : Level} (A B S T : Set a) : Set a where
  exchange : (S → A) → (B → T) → Exchange A B S T

instance ProfunctorExchange : {a : Level}
                            → {A B : Set a}
                            → Profunctor (Exchange A B)

dimap ⦃ ProfunctorExchange ⦄ f g (exchange sa bt) = exchange (sa ∘ f) (g ∘ bt)

instance FunctorExchange : {a : Level}
                         → {A B S : Set a}
                         → Functor (Exchange A B S)

map ⦃ FunctorExchange ⦄ f (exchange sa bt) = exchange sa (f ∘ bt)

Iso : {a b : Level}
    → {P : Set a → Set b → Set (a ⊔ b)}
    → ⦃ _ : Profunctor P ⦄
    → {F : Set a → Set b}
    → ⦃ _ : Functor F ⦄
    → (S T A B : Set a)
    → Set (a ⊔ b)
Iso {P = P} {F = F} S T A B = P A (F B) → P S (F T)

SimpleIso : {a : Level}
          → {P : Set a → Set a → Set a}
          → ⦃ _ : Profunctor P ⦄
          → {F : Set a → Set a}
          → ⦃ _ : Functor F ⦄
          → (S A : Set a)
          → Set a
SimpleIso {P = P} {F = F} S A = Iso {P = P} {F = F} S S A A

AnIso : {a : Level} → (S T A B : Set a) → Set a
AnIso S T A B = Exchange A B A (Identity B) → Exchange A B S (Identity S)

SimpleAnIso : {a : Level} → (S A : Set a) → Set a
SimpleAnIso S A = AnIso S S A A

iso : {a b : Level}
    → {P : Set a → Set b → Set (a ⊔ b)}
    → ⦃ _ : Profunctor P ⦄
    → {F : Set a → Set b}
    → ⦃ _ : Functor F ⦄
    → {S T A B : Set a}
    → (S → A)
    → (B → T)
    → Iso {P = P} {F = F} S T A B
iso sa bt = dimap sa (map bt)

Lens : {a b : Level}
     → {F : Set a → Set b}
     → ⦃ _ : Functor F ⦄
     → (S T A B : Set a)
     → Set (a ⊔ b)
Lens {F = F} S T A B = (A → F B) → (S → F T)

SimpleLens : {a b : Level}
           → {F : Set a → Set b}
           → ⦃ _ : Functor F ⦄
           → (S A : Set a)
           → Set (a ⊔ b)
SimpleLens {F = F} S A = Lens {F = F} S S A A

Setter : {a : Level} → (S T A B : Set a) → Set a
Setter S T A B = (A → Identity B) → S → Identity T

SimpleSetter : {a : Level} → (S A : Set a) → Set a
SimpleSetter S A = Setter S S A A

Getter : {a : Level} → (R S A : Set a) → Set a
Getter R S A = (A → Const R A) → S → Const R S

SimpleGetter : {a : Level} → (S A : Set a) → Set a
SimpleGetter S A = Getter A S A

view : {a : Level} → {S T A B : Set a} → Lens S T A B → S → A
view l = getConst ∘ l mkConst

{-# INLINE view #-}

over : {a : Level} → {S T A B : Set a} → Lens S T A B → (A → B) → S → T
over l f = runIdentity ∘ l (mkIdentity ∘ f)

{-# INLINE over #-}

set : {a : Level} → {S T A B : Set a} → Lens S T A B → B → S → T
set l a = runIdentity ∘ l (mkIdentity ∘ const a)

{-# INLINE set #-}

_%~_ : {a : Level} → {S T A B : Set a} → Setter S T A B → (A → B) → S → T
_%~_ = over

{-# INLINE _%~_ #-}

_:~_ : {a : Level} → {S T A B : Set a} → Setter S T A B → B → S → T
_:~_ = set

{-# INLINE _:~_ #-}

_∙_ : {a : Level} → {S A : Set a} → S → Getter A S A → A
_∙_ = flip view

{-# INLINE _∙_ #-}

to : {a : Level} → {S A : Set a} → (S → A) → SimpleGetter S A
to k = λ f → mkConst ∘ getConst ∘ f ∘ k

{-# INLINE to #-}

lens : {a b : Level}
     → {S T A B : Set a}
     → {F : Set a → Set b}
     → ⦃ _ : Functor F ⦄
     → (S → A)
     → (S → B → T)
     → Lens {F = F} S T A B
lens sa sbt afb s = sbt s <$> afb (sa s)

{-# INLINE lens #-}
