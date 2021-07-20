module Delude.IO where

open import Agda.Primitive

open import Delude.Functor
open import Delude.Applicative
open import Delude.Monad

postulate IO : ∀ {a} → Set a → Set a

{-# POLARITY IO ++ ++ #-}
{-# BUILTIN IO IO #-}

{-# FOREIGN GHC type AgdaIO a b = IO b #-}
{-# COMPILE GHC IO = type AgdaIO #-}

private
  postulate mapIO : ∀ {a} {A B : Set a} → (A → B) → IO A → IO B
  postulate pureIO : ∀ {a} {A : Set a} → A → IO A
  postulate appIO : ∀ {a} {A B : Set a} → IO (A → B) → IO A → IO B
  postulate bindIO : ∀ {a} {A B : Set a} → IO A → (A → IO B) → IO B
  
{-# COMPILE GHC mapIO = fmap #-}
{-# COMPILE GHC pureIO = pure #-}
{-# COMPILE GHC appIO = (<*>) #-}
{-# COMPILE GHC bindIO = (>>=) #-}

instance FunctorIO : ∀ {a} → Functor {a} IO

map ⦃ FunctorIO ⦄ = mapIO

instance ApplicativeIO : ∀ {a} → Applicative {a} IO

pure ⦃ ApplicativeIO ⦄ = pureIO
_<*>_ ⦃ ApplicativeIO ⦄ = appIO

instance MonadIO : ∀ {a} → Monad {a} IO

_>>=_ ⦃ MonadIO ⦄ = bindIO
