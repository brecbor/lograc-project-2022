open import Level

module Signature where

  data Ground (B : Set) : Set where
    baseᵍ : B → Ground B
    emptyᵍ : Ground B
    unitᵍ : Ground B
    _+ᵍ_ : Ground B → Ground B → Ground B
    _×ᵍ_ : Ground B → Ground B → Ground B

  record LangSignature : Set (suc zero) where
    field
      BaseType : Set
      Const : Set
      ConstArg : Const → Ground BaseType
      ConstResult : Const → Ground BaseType
      ℂ : Set
      par : ℂ → Ground BaseType
      ar : ℂ → Ground BaseType
