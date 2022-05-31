open import Data.Nat             using (ℕ; zero; suc; _≤_; z≤n; s≤s; _<_)
open import Data.Product --        using (Σ; _,_; proj₁; proj₂; Σ-syntax)
open import Data.Sum             using (_⊎_; inj₁; inj₂;  [_,_] )
open import Data.Empty          -- using (⊥; ⊥-elim)
open import Data.Unit            using (⊤; tt)
-- open import Data.List            using (List; []; _∷_; _++_; length; map)
open import Data.List.Properties using (map-id; map-compose)
open import Function using (id; _∘_)

data ℂ : Set where
  leaf : ℂ
  node : ℂ

data Children : Set where
  left : Children
  right : Children

{-
par : ℂ → BaseType
par leaf = unit
par node = nat

ar : ℂ → BaseType
ar leaf = empty
ar node = children 
-}
data Tree (P : ℂ → Set) (A : ℂ → Set) : Set where
  Constr   : ∀(c : ℂ)
           → P c
           → (A c → Tree P A) -- dodala oklepaje
           --------------------
           → Tree P A

leaf1 : Tree (λ { leaf → ⊤
                ; node → ℕ })
             (λ { leaf → ⊥
                ; node → Children })
leaf1 = Constr leaf tt λ { () }

node1 : Tree (λ { leaf → ⊤
                ; node → ℕ })
             (λ { leaf → ⊥
                ; node → Children })
node1 = Constr node 5 (λ { left → Constr leaf tt (λ { () })
                         ; right → Constr leaf tt (λ { () })})

node2 : Tree (λ { leaf → ⊤
                ; node → ℕ })
             (λ { leaf → ⊥
                ; node → Children })
node2 = Constr node 5 (λ { left → {! leaf1  !}
                         ; right → Constr leaf tt (λ { () })})
