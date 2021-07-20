module Delude.IO where

open import Agda.Primitive

open import Delude.Functor
open import Delude.Applicative
open import Delude.Monad
open import Delude.String
open import Delude.Unit

postulate IO : ∀ {a} → Set a → Set a

{-# POLARITY IO ++ ++ #-}
{-# BUILTIN IO IO #-}

{-# FOREIGN GHC type AgdaIO a b = IO b #-}
{-# COMPILE GHC IO = type AgdaIO #-}

private
  postulate
    mapIO : ∀ {a b} {A : Set a} {B : Set b} → (A → B) → IO A → IO B
    pureIO : ∀ {a} {A : Set a} → A → IO A
    appIO : ∀ {a b} {A : Set a} {B : Set b} → IO (A → B) → IO A → IO B
    bindIO : ∀ {a b} {A : Set a} {B : Set b} → IO A → (A → IO B) → IO B

{-# COMPILE GHC mapIO = \_ _ _ _ -> fmap #-}
{-# COMPILE GHC pureIO = \_ _ -> pure #-}
{-# COMPILE GHC appIO = \_ _ _ _ -> (<*>) #-}
{-# COMPILE GHC bindIO = \_ _ _ _ -> (>>=) #-}

instance FunctorIO : ∀ {a} → Functor {a} IO

map ⦃ FunctorIO ⦄ = mapIO

instance ApplicativeIO : ∀ {a} → Applicative {a} IO

pure ⦃ ApplicativeIO ⦄ = pureIO
_<*>_ ⦃ ApplicativeIO ⦄ = appIO

instance MonadIO : ∀ {a} → Monad {a} IO

_>>=_ ⦃ MonadIO ⦄ = bindIO

postulate
  putStrLn : String → IO ⊤
  getStrLn : IO String

{-# FOREIGN GHC import qualified Data.Text.IO #-}

{-# COMPILE GHC putStrLn = Data.Text.IO.putStrLn #-}
{-# COMPILE GHC getStrLn = Data.Text.IO.getLine #-}
