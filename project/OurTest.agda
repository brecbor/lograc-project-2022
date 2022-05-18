module OurTest where


open import Data.Unit            using (⊤; tt)
open import Data.Empty
open import Data.Nat
open import Data.Product

data Children : Set where
  left : Children
  right : Children

data BaseType : Set where
  nat : BaseType
  empty : BaseType
  unit : BaseType
  children : BaseType

I : BaseType → Set
I nat = ℕ
I empty = ⊥
I unit = ⊤
I children = Children


data ℂ : Set where
  leaf : ℂ
  node : ℂ

par : ℂ → BaseType
par leaf = unit
par node = nat

ar : ℂ → BaseType
ar leaf = empty
ar node = children

open import Interpreter BaseType I ℂ par ar
open import STLC BaseType I ℂ par ar


program : (x : ⊤) → ⊤
program = ⟦ unit ⟧ᵢ

program2 : (x : ⊤) → ℕ
program2 = ⟦ const 5 ⟧ᵢ 

program3 : (x : ⊤) →  Σ ℕ (λ _ → ℕ) -- Agda.Builtin.Sigma.Σ ℕ (λ _ → ℕ)
program3 = ⟦ const 5 ؛ const 4 ⟧ᵢ

program4 : ℕ
program4 = ⟦ fst (const 5 ؛ const 4) ⟧ᵢ tt

program5 : Tree
program5 = ⟦ constr node 42 aux-tree ⟧ᵢ tt
  where
    aux-tree : Children → [] ⊢ tree
    aux-tree left = constr leaf tt λ { () }
    aux-tree right = constr node 9 λ { left → constr leaf tt λ { () }
                                     ; right → constr leaf tt λ { () } }
{-                                     
program6 : ?
program6 = ⟦ fold (constr node 42 aux-tree) () ⟧ᵢ tt
  where
    aux-tree : Children → [] ⊢ tree
    aux-tree left = constr leaf tt λ { () }
    aux-tree right = constr node 9 λ { left → constr leaf tt λ { () }
                                     ; right → constr leaf tt λ { () } }
-}
{-
program7 : ⟦ ([] ∷ base nat) ∷ base children ⟧ₑ → ℕ
program7 = ⟦ {! var ? ?  !} ⟧ᵢ
-}