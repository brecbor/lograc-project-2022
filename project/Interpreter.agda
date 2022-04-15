module Interpreter where

open import Data.Nat             using (ℕ; zero; suc; _≤_; z≤n; s≤s; _<_)
open import Data.Product --        using (Σ; _,_; proj₁; proj₂; Σ-syntax)
open import Data.Sum             using (_⊎_; inj₁; inj₂; [_,_])
open import Data.Empty           using (⊥; ⊥-elim)
open import Data.Unit            using (⊤; tt)
open import Data.List            using (List; []; _∷_; _++_; length; map)
open import Data.List.Properties using (map-id; map-compose)


open import STLC


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
⟦ var x {{ ∈-here }} ⟧ᵢ = λ { (y , ys) → y }
⟦ var x {{ ∈-there }} ⟧ᵢ = λ { (y , ys) → ⟦ var x ⟧ᵢ ys }
⟦ const {Γ} {A} c ⟧ᵢ = λ ctx → c
⟦ ⁅⁆ ⟧ᵢ = λ _ → tt
⟦ absurd t ⟧ᵢ = {!!}
⟦ t ؛ u ⟧ᵢ = λ ctx →  ⟦ t ⟧ᵢ ctx , ⟦ u ⟧ᵢ ctx
⟦ fst t ⟧ᵢ = λ ctx → proj₁ (⟦ t ⟧ᵢ ctx)
⟦ snd t ⟧ᵢ = λ ctx → proj₂ (⟦ t ⟧ᵢ ctx)
⟦ inl t ⟧ᵢ = λ ctx → inj₁ (⟦ t ⟧ᵢ ctx)
⟦ inr t ⟧ᵢ = λ ctx → inj₂ (⟦ t ⟧ᵢ ctx)
⟦ case {Γ} {A₁} {A₂} {B} t u₁ u₂ ⟧ᵢ = λ ctx → {!!} --  {!⟦ t [ u₁ , u₂ ] ⟧ᵢ ctx!}
⟦ fun {Γ} {A} {B} t ⟧ᵢ = {!!} {- λ ctx → λ z →  ⟦ x ⟧ᵢ (add-to-ctx ctx z) 
  where
    add-to-ctx : ⟦ Γ ⟧ₑ → ⟦ A ⟧ → ⟦ Γ ++ [ A ] ⟧ₑ
    add-to-ctx ctx z = {!ctx!} -}
⟦ app t u ⟧ᵢ = {!!}




