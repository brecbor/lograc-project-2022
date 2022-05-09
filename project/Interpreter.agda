module Interpreter where

open import Data.Nat             using (ℕ; zero; suc; _≤_; z≤n; s≤s; _<_)
open import Data.Product --        using (Σ; _,_; proj₁; proj₂; Σ-syntax)
open import Data.Sum             using (_⊎_; inj₁; inj₂;  [_,_] )
open import Data.Empty          -- using (⊥; ⊥-elim)
open import Data.Unit            using (⊤; tt)
-- open import Data.List            using (List; []; _∷_; _++_; length; map)
open import Data.List.Properties using (map-id; map-compose)
open import Function using (id; _∘_)


open import STLC


⟦_⟧ : Type → Set
⟦ base b ⟧ = I b
⟦ unit ⟧ = ⊤
⟦ empty ⟧ = ⊥
⟦ A ×ᵗ B ⟧ = ⟦ A ⟧ × ⟦ B ⟧
⟦ A ⇒ᵗ B ⟧ = ⟦ A ⟧ → ⟦ B ⟧
⟦ A +ᵗ B ⟧ = ⟦ A ⟧ ⊎ ⟦ B ⟧
⟦ tree ⟧ = Tree

⟦_⟧ₑ : Ctx → Set
⟦ [] ⟧ₑ = ⊥
⟦ Γ ∷ A ⟧ₑ = ⟦ Γ ⟧ₑ × ⟦ A ⟧

aux-proj : {A : Type} {Γ : Ctx} → {{A ∈ Γ}} → ⟦ Γ ⟧ₑ → ⟦ A ⟧
aux-proj {{ ∈-here }} (_ , x) = x
aux-proj {{ ∈-there }} (xs , _) = aux-proj xs

⟦_⟧ᵢ : {Γ : Ctx} {A : Type} → Γ ⊢ A → (⟦ Γ ⟧ₑ → ⟦ A ⟧)
⟦ var x ⟧ᵢ = λ ctx → aux-proj ctx
⟦ const {Γ} {A} c ⟧ᵢ = λ ctx → c
⟦ unit ⟧ᵢ = λ _ → tt
⟦ absurd t ⟧ᵢ =  ⊥-elim ∘ ⟦ t ⟧ᵢ
⟦ t ؛ u ⟧ᵢ = λ ctx →  ⟦ t ⟧ᵢ ctx , ⟦ u ⟧ᵢ ctx
⟦ fst t ⟧ᵢ = λ ctx → proj₁ (⟦ t ⟧ᵢ ctx)
⟦ snd t ⟧ᵢ = λ ctx → proj₂ (⟦ t ⟧ᵢ ctx)
⟦ inl t ⟧ᵢ = λ ctx → inj₁ (⟦ t ⟧ᵢ ctx)
⟦ inr t ⟧ᵢ = λ ctx → inj₂ (⟦ t ⟧ᵢ ctx)
⟦ case t u₁ u₂ ⟧ᵢ = λ ctx → [ ( λ z → ⟦  u₁ ⟧ᵢ (ctx , z) ) , (( λ z → ⟦  u₂ ⟧ᵢ (ctx , z) )) ] ((⟦ t ⟧ᵢ ctx)) 
⟦ fun t ⟧ᵢ = λ ctx → λ z → ⟦ t ⟧ᵢ (ctx , z)
⟦ app t u ⟧ᵢ = λ ctx → (⟦ t ⟧ᵢ ctx) (⟦ u ⟧ᵢ ctx)
⟦ constr c args ⟧ᵢ = λ ctx → Constr c λ i → ⟦ args i ⟧ᵢ ctx




