module Delude.Semigroup where

record Semigroup {a} (A : Set a) : Set a where
  infixr 6 _∙_
  field _∙_ : A → A → A

open Semigroup ⦃ ... ⦄ public
