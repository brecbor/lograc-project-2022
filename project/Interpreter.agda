module Interpreter where

open import Data.Nat             using (ℕ; zero; suc; _≤_; z≤n; s≤s; _<_)
open import Data.Product         using (Σ; _,_; proj₁; proj₂; Σ-syntax)
open import Data.Sum             using (_⊎_; inj₁; inj₂)
open import Data.Empty           using (⊥; ⊥-elim)
import Data.Unit
open import Data.List            using (List; []; _∷_; [_]; _++_; length; map)
open import Data.List.Properties using (map-id; map-compose)

open import STLC

postulate I : BaseType → Set


⟦_⟧ : Type → Set
⟦ base b ⟧ = {!!}
⟦ unit ⟧ = {!!}
⟦ empty ⟧ = {!!}
⟦ A × B ⟧ = {!!}
⟦ A ⇒ B ⟧ = {!!}
⟦ A + B ⟧ = {!!}

