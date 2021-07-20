module Delude.String where

open import Agda.Primitive

open import Delude.Nat
open import Delude.Bool
open import Delude.List
open import Delude.Char

postulate String : Set

{-# BUILTIN STRING String #-}

primitive
  primStringToList : String → List Char
  primStringFromList : List Char → String
  primStringAppend : String → String → String
  primStringEquality : String → String → Bool
  primShowChar : Char → String
  primShowString : String → String
  primShowNat : ℕ → String
