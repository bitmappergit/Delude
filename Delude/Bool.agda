module Delude.Bool where

open import Agda.Primitive

data Bool : Set where
  #t : Bool
  #f : Bool

{-# BUILTIN BOOL Bool #-}
{-# BUILTIN TRUE #t #-}
{-# BUILTIN FALSE #f #-}

¬ : Bool → Bool
¬ #t = #f
¬ #f = #t

{-# INLINE ¬ #-}

_∧_ : Bool → Bool → Bool
#t ∧ #t = #t
#f ∧ #f = #f
#t ∧ #f = #f
#f ∧ #t = #f

_∨_ : Bool → Bool → Bool
#t ∨ #t = #t
#f ∨ #f = #f
#t ∨ #f = #t
#f ∨ #t = #t

infix 0 if_then_else_

if_then_else_ : {a : Level} → {A : Set a} → Bool → A → A → A
if #t then x else _ = x
if #f then _ else y = y
