module STLC (BaseType : Set) where


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
  _×_ : Type → Type → Type
  _⇒_ : Type → Type → Type
  _+_ : Type → Type → Type

infixr 6 _×_
infixr 5 _+_
infixr 4 _⇒_

Ctx = List Type

infixl 2 _⊢_
data _⊢_ : Ctx → Type → Set where

  -- product

  ∧-intro  : {Δ : Hypotheses}
           → {A ψ : Formula}
           → Δ ⊢ A
           → Δ ⊢ ψ
           -------------------
           → Δ ⊢ A ∧ ψ
          
  ∧-elim₁  : {Δ : Hypotheses}
           → {A ψ : Formula}
           → Γ ⊢ A ∧ ψ
           -------------------
           → Γ ⊢ A

  ∧-elim₂  : {Γ : Hypotheses}
           → {A ψ : Formula}
           → Γ ⊢ A ∧ ψ
           -------------------
           → Γ ⊢ ψ

  -- sum

  ∨-intro₁ : {Γ : Hypotheses}
           → {A ψ : Formula}
           → Γ ⊢ A
           ------------------
           → Γ ⊢ A ∨ ψ

  ∨-intro₂ : {Γ : Hypotheses}
           → {A ψ : Formula}
           → Γ ⊢ ψ
           -------------------
           → Γ ⊢ A ∨ ψ

  ∨-elim   : {Γ : Hypotheses}
           → {A₁ A₂ ψ : Formula}
           → Γ ⊢ A₁ ∨ A₂
           → Γ ++ [ A₁ ] ⊢ ψ
           → Γ ++ [ A₂ ] ⊢ ψ
           ---------------------
           → Γ ⊢ ψ

  -- lambda

  ⇒-intro  : {Γ : Ctx}
           → {A B : Type}
           → Γ ++ [ A ] ⊢ B
           --------------------
           → Γ ⊢ A ⇒ B

  ⇒-elim   : {Γ : Ctx}
           → {A B : Type}
           → Γ ⊢ A ⇒ B
           → Γ ⊢ A
           -------------------
           → Γ ⊢ B  
