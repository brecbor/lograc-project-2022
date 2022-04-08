module Interpreter where

open import Data.Nat             using (ℕ; zero; suc; _≤_; z≤n; s≤s; _<_)
open import Data.Product --         using (Σ; _,_; proj₁; proj₂; Σ-syntax)
open import Data.Sum             using (_⊎_; inj₁; inj₂)
open import Data.Empty           using (⊥; ⊥-elim)
open import Data.Unit            using (⊤)
open import Data.List            using (List; []; _∷_; [_]; _++_; length; map)
open import Data.List.Properties using (map-id; map-compose)


open import STLC

postulate I : BaseType → Set


⟦_⟧ : Type → Set
⟦ base b ⟧ = I b
⟦ unit ⟧ = ⊤
⟦ empty ⟧ = ⊥
⟦ A ×ᵗ B ⟧ = ⟦ A ⟧ × ⟦ B ⟧
⟦ A ⇒ᵗ B ⟧ = ⟦ A ⟧ → ⟦ B ⟧
⟦ A +ᵗ B ⟧ = ⟦ A ⟧ ⊎ ⟦ B ⟧

⟦_⟧ₑ : Ctx → Set
⟦ [] ⟧ₑ    = ⊥
⟦ A ∷ Γ ⟧ₑ = ⟦ A ⟧ × ⟦ Γ ⟧ₑ

⟦_⟧ᵢ : {Γ : Ctx} {A : Type} → Γ ⊢ A → (⟦ Γ ⟧ₑ → ⟦ A ⟧)
⟦ var _ ⟧ᵢ = {!!}
⟦ base-intro ⟧ᵢ = {!!}
⟦ unit-intro ⟧ᵢ = {!!}
⟦ empty-elim x ⟧ᵢ = {!!}
⟦ ×-intro x x₁ ⟧ᵢ = {!!}
⟦ ×-fst x ⟧ᵢ = {!!}
⟦ ×-snd x ⟧ᵢ = {!!}
⟦ inl x ⟧ᵢ = {!!}
⟦ inr x ⟧ᵢ = {!!}
⟦ case x x₁ x₂ ⟧ᵢ = {!!}
⟦ ⇒-intro x ⟧ᵢ = {!!}
⟦ ⇒-elim x x₁ ⟧ᵢ = {!!}

