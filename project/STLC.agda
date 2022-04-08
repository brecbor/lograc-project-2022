module STLC where

postulate BaseType : Set

-- in the end we will change the above lines to
-- module STLC (BaseType : Set) where

open import Data.Nat             using (ℕ; zero; suc; _≤_; z≤n; s≤s; _<_)
open import Data.Product         using (Σ; _,_; proj₁; proj₂; Σ-syntax)
open import Data.Sum             using (_⊎_; inj₁; inj₂)
open import Data.Empty           using (⊥; ⊥-elim)
import Data.Unit
open import Data.List            using (List; []; _∷_; [_]; _++_; length; map)
open import Data.List.Properties using (map-id; map-compose)


data Type : Set where
  base : BaseType → Type
  unit : Type
  empty : Type
  _×ᵗ_ : Type → Type → Type
  _⇒ᵗ_ : Type → Type → Type
  _+ᵗ_ : Type → Type → Type

infixr 6 _×ᵗ_
infixr 5 _+ᵗ_
infixr 4 _⇒ᵗ_

Ctx = List Type

infix 3 _∈_
data _∈_ {A : Set} : A → List A → Set where
  instance
    ∈-here  : {x : A} → {xs : List A} → x ∈ (x ∷ xs)
    ∈-there : {x y : A} {xs : List A} → {{x ∈ xs}} → x ∈ (y ∷ xs)


infixl 2 _⊢_
data _⊢_ : Ctx → Type → Set where

  -- Context

  var      : {Γ : Ctx}
           → (A : Type)
           → {{A ∈ Γ}}
           -----------------
           → Γ ⊢ A

  -- base

  base-intro  : {Γ : Ctx}
              → {A : BaseType}
              ------------------
              → Γ ⊢ base A

  -- unit

  unit-intro  : {Γ : Ctx}
              ------------------
              → Γ ⊢ unit

  -- empty

  empty-elim   : {Γ : Ctx}
               → {A : Type}
               → Γ ⊢ empty
               -------------------
               → Γ ⊢ A

  -- product

  ×-intro  : {Γ : Ctx}
           → {A B : Type}
           → Γ ⊢ A
           → Γ ⊢ B
           -------------------
           → Γ ⊢ A ×ᵗ B
          
  ×-fst  : {Γ : Ctx}
           → {A B : Type}
           → Γ ⊢ A ×ᵗ B
           -------------------
           → Γ ⊢ A

  ×-snd  : {Γ : Ctx}
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
           → Γ ++ [ A₁ ] ⊢ B
           → Γ ++ [ A₂ ] ⊢ B
           ---------------------
           → Γ ⊢ B

  -- lambda

  ⇒-intro  : {Γ : Ctx}
           → {A B : Type}
           → Γ ++ [ A ] ⊢ B
           --------------------
           → Γ ⊢ A ⇒ᵗ B

  ⇒-elim   : {Γ : Ctx}
           → {A B : Type}
           → Γ ⊢ A ⇒ᵗ B
           → Γ ⊢ A
           -------------------
           → Γ ⊢ B  
