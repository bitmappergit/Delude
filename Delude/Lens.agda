module Delude.Lens where

open import Agda.Primitive

open import Delude.Function
open import Delude.Functor
open import Delude.Identity
open import Delude.Const
open import Delude.Profunctor

record Exchange {a} (A B S T : Set a) : Set a where
  constructor exchange
  field sa : (S → A)
  field bt : (B → T)

instance ProfunctorExchange : ∀ {a} {A B : Set a}
                            → Profunctor (Exchange A B)

dimap ⦃ ProfunctorExchange ⦄ f g (exchange sa bt) = exchange (sa ∘ f) (g ∘ bt)

instance FunctorExchange : ∀ {a} {A S B : Set a}
                         → Functor (Exchange A B S)

map ⦃ FunctorExchange ⦄ f (exchange sa bt) = exchange sa (f ∘ bt)

Iso : ∀ {a} → (S T A B : Set a) → Set (lsuc a)
Iso {a} S T A B = {P : Set a → Set a → Set a} ⦃ _ : Profunctor P ⦄
                → {F : Set a → Set a} ⦃ _ : Functor F ⦄
                → P A (F B)
                → P S (F T)

MonoIso : ∀ {a} → (S A : Set a) → Set (lsuc a)
MonoIso S A = Iso S S A A

AnIso : ∀ {a} → (S T A B : Set a) → Set a
AnIso S T A B = Exchange A B A (Identity B) → Exchange A B S (Identity S)

MonoAnIso : ∀ {a} → (S A : Set a) → Set a
MonoAnIso S A = AnIso S S A A

iso : ∀ {a} {S T A B : Set a} → (S → A) → (B → T) → Iso S T A B
iso sa bt = dimap sa (map bt)

Lens : ∀ {a} → (S T A B : Set a) → Set (lsuc a)
Lens {a} S T A B = {F : Set a → Set a} ⦃ _ : Functor F ⦄
                 → (A → F B)
                 → (S → F T)

MonoLens : ∀ {a} → (S A : Set a) → Set (lsuc a)
MonoLens S A = Lens S S A A

Setter : ∀ {a} → (S T A B : Set a) → Set a
Setter S T A B = (A → Identity B) → (S → Identity T)

MonoSetter : ∀ {a} → (S A : Set a) → Set a
MonoSetter S A = Setter S S A A

Getter : ∀ {a} → (R S A : Set a) → Set a
Getter R S A = (A → Const R A) → (S → Const R S)

MonoGetter : ∀ {a} → (S A : Set a) → Set a
MonoGetter S A = Getter A S A

view : ∀ {a} {S A : Set a} → Getter A S A → S → A
view l = getConst ∘ l mkConst

over : ∀ {a} {S T A B : Set a} → Setter S T A B → (A → B) → S → T
over l f = runIdentity ∘ l (mkIdentity ∘ f)

set : ∀ {a} {S T A B : Set a} → Setter S T A B → B → S → T
set l a = runIdentity ∘ l (mkIdentity ∘ const a)
 
infixr 4 _%~_
infixr 4 _:~_
infixr 4 _at_

_%~_ : ∀ {a} {S T A B : Set a} → Setter S T A B → (A → B) → S → T
_%~_ = over

_:~_ : ∀ {a} {S T A B : Set a} → Setter S T A B → B → S → T
_:~_ = set

_at_ : ∀ {a} {S A : Set a} → S → Getter A S A → A
_at_ = flip view

lens : ∀ {a} {S T A B : Set a} → (S → A) → (S → B → T) → Lens S T A B
lens sa sbt afb s = sbt s <$> afb (sa s)
