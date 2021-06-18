module Delude.Identity where

open import Agda.Primitive

open import Delude.Functor
open import Delude.Applicative
open import Delude.Monad

private
  variable
    a : Level

record Identity (A : Set a) : Set a where
  constructor mkIdentity
  field
    runIdentity : A

open Identity public

instance FunctorIdentity : Functor {a} Identity
instance ApplicativeIdentity : Applicative {a} Identity
instance MonadIdentity : Monad {a} Identity

map ⦃ FunctorIdentity ⦄ f (mkIdentity x) = mkIdentity (f x)

_<*>_ ⦃ ApplicativeIdentity ⦄ (mkIdentity f) (mkIdentity x) = mkIdentity (f x)
pure ⦃ ApplicativeIdentity ⦄ = mkIdentity

_>>=_ ⦃ MonadIdentity ⦄ (mkIdentity v) f = f v
