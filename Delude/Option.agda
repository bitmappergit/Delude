module Delude.Option where

open import Agda.Primitive
open import Delude.Functor
open import Delude.Applicative
open import Delude.Monad

data Option {a} (A : Set a) : Set a where
  some : A → Option A
  none : Option A

instance FunctorOption : ∀ {a} → Functor {a} Option

map ⦃ FunctorOption ⦄ f (some x) = some (f x)
map ⦃ FunctorOption ⦄ _ none = none

instance ApplicativeOption : ∀ {a} → Applicative {a} Option

pure ⦃ ApplicativeOption ⦄ = some

_<*>_ ⦃ ApplicativeOption ⦄ (some f) (some x) = some (f x)
_<*>_ ⦃ ApplicativeOption ⦄ (some _) none = none
_<*>_ ⦃ ApplicativeOption ⦄ none (some _) = none
_<*>_ ⦃ ApplicativeOption ⦄ none none = none

instance MonadOption : ∀ {a} → Monad {a} Option

_>>=_ ⦃ MonadOption ⦄ (some x) f = f x
_>>=_ ⦃ MonadOption ⦄ none _ = none
