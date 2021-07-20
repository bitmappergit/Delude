module Delude.Char where

open import Agda.Primitive

open import Delude.Nat
open import Delude.Bool

postulate Char : Set

{-# BUILTIN CHAR Char #-}

primitive
  primIsLower : Char → Bool
  primIsDigit : Char → Bool
  primIsAlpha : Char → Bool
  primIsSpace : Char → Bool
  primIsAscii : Char → Bool
  primIsLatin1 : Char → Bool
  primIsPrint : Char → Bool
  primIsHexDigit : Char → Bool
  primToUpper : Char → Char
  primToLower : Char → Char
  primCharToNat : Char → ℕ
  primNatToChar : ℕ → Char
  primCharEquality : Char → Char → Bool
