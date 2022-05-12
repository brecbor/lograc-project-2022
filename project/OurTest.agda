module OurTest where

open import Data.Nat

data BaseType : Set where
  nat : BaseType

I : BaseType → Set
I nat = ℕ



open import Interpreter
-- open import STLC




  
