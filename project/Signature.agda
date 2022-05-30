open import Level

module Signature where

  data Ground (B : Set) : Set where
    baseᵍ : B → Ground B
    emptyᵍ : Ground B
    unitᵍ : Ground B
    _+ᵍ_ : Ground B → Ground B → Ground B
    _×ᵍ_ : Ground B → Ground B → Ground B

  record Signature : Set (suc zero) where
    field
      BaseType : Set
      I : BaseType → Set
      BaseDef : BaseType → Set
      BaseOp : {A : BaseType} → BaseDef A → I A → I A → I A
      ℂ : Set
      par : ℂ → Ground BaseType
      ar : ℂ → Ground BaseType
