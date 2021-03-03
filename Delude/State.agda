module Delude.State where

open import Agda.Primitive

open import Delude.Function
open import Delude.Functor
open import Delude.Applicative
open import Delude.Monad
open import Delude.Product
open import Delude.Identity
open import Delude.Unit
open import Delude.Lens
open import Delude.Semiring
open import Delude.Ring

record StateT {a : Level} (S : Set a) (M : Set a → Set a) (A : Set a) : Set a where
  constructor mkStateT
  field runStateT : S → M (A × S)

open StateT public

state : {a : Level}
      → {S A : Set a}
      → {M : Set a → Set a}
      → ⦃ _ : Monad M ⦄
      → (S → (A × S))
      → StateT S M A
state f = mkStateT (return ∘ f)

State : {a : Level} → Set a → Set a → Set a
State S A = StateT S Identity A

runState : {a : Level} → {S A : Set a} → State S A → S → (A × S)
runState m = runIdentity ∘ runStateT m

evalState : {a : Level} → {S A : Set a} → State S A → S → A
evalState m s = fst (runState m s)

instance FunctorStateT : {a : Level}
                       → {S : Set a}
                       → {M : Set a → Set a}
                       → ⦃ _ : Monad M ⦄
                       → Functor (StateT S M)

map ⦃ FunctorStateT ⦄ f m = mkStateT λ s → map (λ (a , x) → (f a , x)) $ runStateT m s

instance ApplicativeStateT : {a : Level}
                           → {S : Set a}
                           → {M : Set a → Set a}
                           → ⦃ _ : Monad M ⦄
                           → Applicative (StateT S M)

pure ⦃ ApplicativeStateT ⦄ a = mkStateT λ s → return (a , s)
_<*>_ ⦃ ApplicativeStateT ⦄ (mkStateT mf) (mkStateT mx) = mkStateT λ s → do
  (f , sf) ← mf s
  (x , sx) ← mx sf
  return (f x , sx)

instance MonadStateT : {a : Level}
                     → {S : Set a}
                     → {M : Set a → Set a}
                     → ⦃ _ : Monad M ⦄
                     → Monad (StateT S M)

_>>=_ ⦃ MonadStateT ⦄ m k = mkStateT λ s → do
  (a , ns) ← runStateT m s
  runStateT (k a) ns

gets : {a : Level}
     → {S A : Set a}
     → {M : Set a → Set a}
     → ⦃ _ : Monad M ⦄
     → (S → A)
     → StateT S M A
gets f = state λ s → (f s , s)

modify : {a : Level}
       → {S A : Set a}
       → {M : Set a → Set a}
       → ⦃ _ : Monad M ⦄
       → (S → S)
       → StateT S M ⊤
modify f = state λ s → (unit , f s)

get : {a : Level}
    → {S : Set a}
    → {M : Set a → Set a}
    → ⦃ _ : Monad M ⦄
    → StateT S M S
get = state λ s → (s , s)

_%=_ : {a : Level} → {S A : Set a} → SimpleSetter S A → (A → A) → State S ⊤
_%=_ l f = modify {A = ⊤} (l %~ f)

_:=_ : {a : Level} → {S A : Set a} → SimpleSetter S A → A → State S ⊤
_:=_ l x = modify {A = ⊤} (l :~ x)

_+=_ : {a : Level} → {S A : Set a} → ⦃ _ : Semiring A ⦄ → SimpleSetter S A → A → State S ⊤
_+=_ l f = modify {A = ⊤} (l %~ _+ f)

_-=_ : {a : Level} → {S A : Set a} → ⦃ _ : Ring A ⦄ → SimpleSetter S A → A → State S ⊤
_-=_ l f = modify {A = ⊤} (l %~ _- f)

use : {a : Level} → {S A : Set a} → SimpleGetter S A → State S A
use = gets ∘ view
