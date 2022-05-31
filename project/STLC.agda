open import Signature

module STLC (𝕊 : Signature.Signature) where
{-
postulate BaseType : Set
postulate I : BaseType → Set

postulate ℂ : Set
postulate par : ℂ → BaseType  -- TODO: enkrat bo BaseType sel v GroundType
postulate ar : ℂ → BaseType
-}
-- in the end we will change the above lines to
-- module STLC (BaseType : Set) where
-- (ℂ : Set) (ar : ℂ → Set)

open import Data.Nat             using (ℕ; zero; suc; _≤_; z≤n; s≤s; _<_)
open import Data.Product         using (Σ; _,_; proj₁; proj₂; Σ-syntax)
open import Data.Sum             using (_⊎_; inj₁; inj₂)
open import Data.Empty           using (⊥; ⊥-elim)
import Data.Unit
-- open import Data.List            using (List; []; _∷_; [_]; _++_; length; map)
open import Data.List.Properties using (map-id; map-compose)

open Signature.Signature 𝕊

data Type : Set where
  base : BaseType → Type
  unit : Type
  empty : Type
  _×ᵗ_ : Type → Type → Type
  _⇒ᵗ_ : Type → Type → Type
  _+ᵗ_ : Type → Type → Type
  tree : ℂ → Type

infixr 6 _×ᵗ_
infixr 5 _+ᵗ_
infixr 4 _⇒ᵗ_

J : Signature.Ground BaseType → Type
J (baseᵍ B) = base B
J emptyᵍ = empty
J unitᵍ = unit
J (A +ᵍ B) = J A +ᵗ J B
J (A ×ᵍ B) = J A ×ᵗ J B


-- Ctx = List Type
data List' (A : Set) : Set where
  [] : List' A
  _∷_ : List' A → A → List' A

Ctx = List' Type

infix 3 _∈_
data _∈_ {A : Set} : A → List' A → Set where
    ∈-here  : {x : A} → {xs : List' A} → x ∈ (xs ∷ x)
    ∈-there : {x y : A} {xs : List' A} → x ∈ xs → x ∈ (xs ∷ y)

infixl 2 _⊢_
data _⊢_ : Ctx → Type → Set where
{-
  -- Context
  LET_IN_  : {Γ : Ctx}
           → {A : Type}
           → {B : Type}
           → Γ ⊢ A
           → Γ ⊢ A ⇒ᵗ B
           -----------------------
           → Γ ⊢ B


let x = V in W
let V in W

(lambda x . W) V
app (fun W) V

  -}
  var      : {Γ : Ctx}
           → {A : Type}
           → A ∈ Γ
           -----------------
           → Γ ⊢ A

  -- base

  const       : {Γ : Ctx}
              → {A : BaseType}
              → I A
              ------------------
              → Γ ⊢ base A

  -- unit

  unit          : {Γ : Ctx}
              ------------------
              → Γ ⊢ unit

  -- empty

  absurd       : {Γ : Ctx}
               → {A : Type}
               → Γ ⊢ empty
               -------------------
               → Γ ⊢ A

  -- product

  _؛_      : {Γ : Ctx}
           → {A B : Type}
           → Γ ⊢ A
           → Γ ⊢ B
           -------------------
           → Γ ⊢ A ×ᵗ B

  fst      : {Γ : Ctx}
           → {A B : Type}
           → Γ ⊢ A ×ᵗ B
           -------------------
           → Γ ⊢ A

  snd      : {Γ : Ctx}
           → {A B : Type}
           → Γ ⊢ A ×ᵗ B
           -------------------
           → Γ ⊢ B

  -- sum

  inl      : {Γ : Ctx}
           → {A B : Type}
           → Γ ⊢ A
           ------------------
           → Γ ⊢ A +ᵗ B

  inr      : {Γ : Ctx}
           → {A B : Type}
           → Γ ⊢ B
           -------------------
           → Γ ⊢ A +ᵗ B

  case     : {Γ : Ctx}
           → {A₁ A₂ B : Type}
           → Γ ⊢ A₁ +ᵗ A₂
           → Γ ∷ A₁ ⊢ B
           → Γ ∷ A₂ ⊢ B
           ---------------------
           → Γ ⊢ B

  -- lambda

  fun      : {Γ : Ctx}
           → {A B : Type}
           → Γ ∷ A ⊢ B
           --------------------
           → Γ ⊢ A ⇒ᵗ B

  app      : {Γ : Ctx}
           → {A B : Type}
           → Γ ⊢ A ⇒ᵗ B
           → Γ ⊢ A
           -------------------
           → Γ ⊢ B

  -- tree

  constr   : {Γ : Ctx}
           → ∀(c : ℂ)
           → Γ ⊢ J (par c)
           → Γ ∷ J (ar c) ⊢ tree c
           --------------------
           → Γ ⊢ tree c

  fold     : {Γ : Ctx}
           → {c₂ : ℂ}
           → ∀{A : Type}
           → (Γ ⊢ tree c₂)
           → ( ∀(c : ℂ) →  Γ ⊢ J (par c) ⇒ᵗ (J (ar c) ⇒ᵗ A) ⇒ᵗ A)
           --------------------
           → Γ ⊢ A

  -- functions for base types

  baseFun  : {Γ : Ctx}
           → {A : BaseType}
           → BaseDef A
           → Γ ⊢ base A
           → Γ ⊢ base A
           --------------------
           → Γ ⊢ base A
