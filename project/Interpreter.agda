open import Data.Nat             using (ℕ; zero; suc; _≤_; z≤n; s≤s; _<_)
open import Data.Product --        using (Σ; _,_; proj₁; proj₂; Σ-syntax)
open import Data.Sum             using (_⊎_; inj₁; inj₂;  [_,_] )
open import Data.Empty          -- using (⊥; ⊥-elim)
open import Data.Unit            using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)
-- open import Data.List            using (List; []; _∷_; _++_; length; map)
open import Data.List.Properties using (map-id; map-compose)
open import Function using (id; _∘_)

import STLC
open import Signature

module Interpreter (𝕊 : Signature.Signature) where

open STLC 𝕊
open Signature.Signature 𝕊

data Tree (P : ℂ → Set) (A : ℂ → Set) : Set where
  Constr   : ∀(c : ℂ)
           → P c
           → (A c → Tree P A)
           --------------------
           → Tree P A

Fold     : {P : ℂ → Set} {A : ℂ → Set} {B : Set}
           → (∀ (c : ℂ) → P c → (A c → B) → B)
           → Tree P A
           --------------------
           → B

Fold f (Constr c p t) = f c p (Fold f ∘ t)

⟦_⟧ᵍ : Ground BaseType → Set
⟦ baseᵍ b ⟧ᵍ = I b
⟦ emptyᵍ ⟧ᵍ = ⊥
⟦ unitᵍ ⟧ᵍ = ⊤
⟦ A +ᵍ B ⟧ᵍ = ⟦ A ⟧ᵍ ⊎ ⟦ B ⟧ᵍ
⟦ A ×ᵍ B ⟧ᵍ = ⟦ A ⟧ᵍ × ⟦ B ⟧ᵍ

⟦_⟧ : Type → Set
⟦ base b ⟧ = I b
⟦ unit ⟧ = ⊤
⟦ empty ⟧ = ⊥
⟦ A ×ᵗ B ⟧ = ⟦ A ⟧ × ⟦ B ⟧
⟦ A ⇒ᵗ B ⟧ = ⟦ A ⟧ → ⟦ B ⟧
⟦ A +ᵗ B ⟧ = ⟦ A ⟧ ⊎ ⟦ B ⟧
⟦ tree ⟧ = Tree (λ c → ⟦ par c ⟧ᵍ) (λ c → ⟦ ar c ⟧ᵍ)  -- termination checking failed

⟦⟧ᵍ≡⟦J⟧ : (A : Ground BaseType) → ⟦ A ⟧ᵍ ≡ ⟦ J A ⟧
⟦⟧ᵍ≡⟦J⟧ (baseᵍ b) = {!!}
⟦⟧ᵍ≡⟦J⟧ emptyᵍ = {!!}
⟦⟧ᵍ≡⟦J⟧ unitᵍ = {!!}
⟦⟧ᵍ≡⟦J⟧ (A +ᵍ B) = {!!}
⟦⟧ᵍ≡⟦J⟧ (A ×ᵍ B) = {!!}

⟦_⟧ₑ : Ctx → Set
⟦ [] ⟧ₑ = ⊤ -- ⊥
⟦ Γ ∷ A ⟧ₑ = ⟦ Γ ⟧ₑ × ⟦ A ⟧


aux-proj : {A : Type} {Γ : Ctx} → A ∈ Γ → ⟦ Γ ⟧ₑ → ⟦ A ⟧
aux-proj ∈-here (_ , x) = x
aux-proj (∈-there index) (xs , _) = aux-proj index xs

lemica : {A B : Set} → A ≡ B → A → B
lemica refl p = p

⟦_⟧ᵢ : {Γ : Ctx} {A : Type} → Γ ⊢ A → (⟦ Γ ⟧ₑ → ⟦ A ⟧)
⟦ var index ⟧ᵢ η = aux-proj index η
⟦ const {Γ} {A} c ⟧ᵢ η = c
⟦ unit ⟧ᵢ _  = tt
⟦ absurd t ⟧ᵢ =  ⊥-elim ∘ ⟦ t ⟧ᵢ
⟦ t ؛ u ⟧ᵢ η =  ⟦ t ⟧ᵢ  η , ⟦ u ⟧ᵢ  η
⟦ fst t ⟧ᵢ η = proj₁ (⟦ t ⟧ᵢ  η)
⟦ snd t ⟧ᵢ η = proj₂ (⟦ t ⟧ᵢ  η)
⟦ inl t ⟧ᵢ η = inj₁ (⟦ t ⟧ᵢ  η)
⟦ inr t ⟧ᵢ η = inj₂ (⟦ t ⟧ᵢ  η)
⟦ case t u₁ u₂ ⟧ᵢ η = [ ( λ z → ⟦  u₁ ⟧ᵢ ( η , z) ) , (( λ z → ⟦  u₂ ⟧ᵢ ( η , z) )) ] ((⟦ t ⟧ᵢ  η))
⟦ fun t ⟧ᵢ η = λ z → ⟦ t ⟧ᵢ (η , z)
⟦ app t u ⟧ᵢ η = (⟦ t ⟧ᵢ  η) (⟦ u ⟧ᵢ  η)
⟦ constr c param args ⟧ᵢ η =  {!   !} -- Constr c param (λ i → ⟦ args i ⟧ᵢ  η)
⟦ fold f t ⟧ᵢ η = Fold (λ c p t' → ⟦ f c ⟧ᵢ ((η , lemica (⟦⟧ᵍ≡⟦J⟧ (par c)) p) , λ x → t' (lemica (sym (⟦⟧ᵍ≡⟦J⟧ (ar c))) x)) ) (⟦ t ⟧ᵢ η) -- Fold (⟦ t ⟧ᵢ  η) λ i → ⟦ f i ⟧ᵢ  η
⟦ baseFun name x y ⟧ᵢ η = BaseOp name (⟦ x ⟧ᵢ η) (⟦ y ⟧ᵢ η)
