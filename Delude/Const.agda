module Delude.Const where

open import Agda.Primitive

open import Delude.Functor
open import Delude.Applicative
open import Delude.Monad

private
  variable
    a b : Level

record Const (A : Set a) (B : Set b) : Set a where
  constructor mkConst
  field getConst : A

open Const public

instance FunctorConst : {A : Set a} → Functor {a} (Const A)

map ⦃ FunctorConst ⦄ f v = mkConst (getConst v)
