module Delude.State where

open import Agda.Primitive

open import Delude.Function
open import Delude.Functor
open import Delude.Applicative
open import Delude.Monad
open import Delude.Product
open import Delude.Identity
open import Delude.Unit.Polymorphic
open import Delude.Lens
open import Delude.Semiring
open import Delude.Ring

record StateT {a b} (S : Set a) (M : Set a → Set b) (A : Set a) : Set (a ⊔ b) where
  constructor mkStateT
  field runStateT : S → M (A × S)

open StateT public

state : ∀ {a b} {S A : Set a} {M : Set a → Set b}
      → ⦃ _ : Monad M ⦄
      → (S → (A × S))
      → StateT S M A
state f = mkStateT (return ∘ f)

State : ∀ {a} → Set a → Set a → Set a
State S A = StateT S Identity A

runState : ∀ {a} {S A : Set a} → State S A → S → (A × S)
runState m = runIdentity ∘ runStateT m

evalState : ∀ {a} {S A : Set a} → State S A → S → A
evalState m s = fst (runState m s)

instance FunctorStateT : ∀ {a b} {S : Set a} {M : Set a → Set b}
                       → ⦃ _ : Monad M ⦄
                       → Functor (StateT S M)

map ⦃ FunctorStateT ⦄ f m = mkStateT λ s → map (λ (a , x) → (f a , x)) (runStateT m s)

instance ApplicativeStateT : ∀ {a b} {S : Set a} {M : Set a → Set b}
                           → ⦃ _ : Monad M ⦄
                           → Applicative (StateT S M)

pure ⦃ ApplicativeStateT ⦄ a = mkStateT λ s → return (a , s)
 
_<*>_ ⦃ ApplicativeStateT ⦄ (mkStateT mf) (mkStateT mx) = mkStateT λ s → do
  (f , sf) ← mf s
  (x , sx) ← mx sf
  return (f x , sx)

instance MonadStateT : ∀ {a b} {S : Set a} {M : Set a → Set b}
                     → ⦃ _ : Monad M ⦄
                     → Monad (StateT S M)

_>>=_ ⦃ MonadStateT ⦄ m k = mkStateT λ s →
  do (a , ns) ← runStateT m s
     runStateT (k a) ns

gets : ∀ {a b} {S A : Set a} {M : Set a → Set b}
     → ⦃ _ : Monad M ⦄
     → (S → A)
     → StateT S M A
gets f = state λ s → (f s , s)

modify : ∀ {a b} {S : Set a} {M : Set a → Set b}
       → ⦃ _ : Monad M ⦄
       → (S → S)
       → StateT S M ⊤
modify f = state λ s → (unit , f s)

get : ∀ {a b} {S : Set a} {M : Set a → Set b}
    → ⦃ _ : Monad M ⦄
    → StateT S M S
get = state λ s → (s , s)

_%=_ : ∀ {a b} {S A : Set a} {M : Set a → Set b}
     → ⦃ _ : Monad M ⦄
     → MonoSetter S A
     → (A → A)
     → StateT S M ⊤
_%=_ l f = modify (l %~ f)

_:=_ : ∀ {a b} {S A : Set a} {M : Set a → Set b}
     → ⦃ _ : Monad M ⦄
     → MonoSetter S A
     → A
     → StateT S M ⊤
_:=_ l x = modify (l :~ x)

_+=_ : ∀ {a b} {S A : Set a} {M : Set a → Set b}
     → ⦃ _ : Monad M ⦄ ⦃ _ : Semiring A ⦄
     → MonoSetter S A
     → A
     → StateT S M ⊤
_+=_ l f = modify (l %~ _+ f)

_-=_ : ∀ {a b} {S A : Set a} {M : Set a → Set b}
     → ⦃ _ : Monad M ⦄ ⦃ _ : Ring A ⦄
     → MonoSetter S A
     → A
     → StateT S M ⊤
_-=_ l f = modify (l %~ _- f)

use : ∀ {a b} {S A : Set a} {M : Set a → Set b}
    → ⦃ _ : Monad M ⦄
    → MonoGetter S A
    → StateT S M A
use = gets ∘ view
