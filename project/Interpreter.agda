module Interpreter (BaseType : Set) (I : BaseType → Set) (BaseDef : BaseType → Set) (BaseOp : {A : BaseType} → BaseDef A → I A → I A → I A) (ℂ : Set) (par : ℂ → BaseType) (ar : ℂ → BaseType) where

open import Data.Nat             using (ℕ; zero; suc; _≤_; z≤n; s≤s; _<_)
open import Data.Product --        using (Σ; _,_; proj₁; proj₂; Σ-syntax)
open import Data.Sum             using (_⊎_; inj₁; inj₂;  [_,_] )
open import Data.Empty          -- using (⊥; ⊥-elim)
open import Data.Unit            using (⊤; tt)
-- open import Data.List            using (List; []; _∷_; _++_; length; map)
open import Data.List.Properties using (map-id; map-compose)
open import Function using (id; _∘_)


open import STLC BaseType I BaseDef BaseOp ℂ par ar


⟦_⟧ : Type → Set
⟦ base b ⟧ = I b
⟦ unit ⟧ = ⊤
⟦ empty ⟧ = ⊥
⟦ A ×ᵗ B ⟧ = ⟦ A ⟧ × ⟦ B ⟧
⟦ A ⇒ᵗ B ⟧ = ⟦ A ⟧ → ⟦ B ⟧
⟦ A +ᵗ B ⟧ = ⟦ A ⟧ ⊎ ⟦ B ⟧
⟦ tree ⟧ = Tree

⟦_⟧ₑ : Ctx → Set
⟦ [] ⟧ₑ = ⊤ -- ⊥
⟦ Γ ∷ A ⟧ₑ = ⟦ Γ ⟧ₑ × ⟦ A ⟧

aux-proj : {A : Type} {Γ : Ctx} → A ∈ Γ → ⟦ Γ ⟧ₑ → ⟦ A ⟧
aux-proj ∈-here (_ , x) = x
aux-proj (∈-there index) (xs , _) = aux-proj index xs

⟦_⟧ᵢ : {Γ : Ctx} {A : Type} → Γ ⊢ A → (⟦ Γ ⟧ₑ → ⟦ A ⟧)
-- ⟦ LET t IN u ⟧ᵢ η = ⟦ app u t ⟧ᵢ η
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
⟦ constr c param args ⟧ᵢ η = Constr c param (λ i → ⟦ args i ⟧ᵢ  η) 
⟦ fold t f ⟧ᵢ η = Fold (⟦ t ⟧ᵢ  η) λ i → ⟦ f i ⟧ᵢ  η
⟦ baseFun name x y ⟧ᵢ η = BaseOp name (⟦ x ⟧ᵢ η) (⟦ y ⟧ᵢ η) 



