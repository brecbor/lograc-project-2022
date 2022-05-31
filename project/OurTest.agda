open import Signature

module OurTest where


open import Data.Unit            using (⊤; tt)
open import Data.Empty
open import Data.Nat
open import Data.Product

data Children : Set where
  left : Children
  right : Children

data BaseType' : Set where
  nat : BaseType'
  children : BaseType'

I' : BaseType' → Set
I' nat = ℕ
I' children = Children

data Const' : Set where
  zero : Const'
  succ : Const'
  plus : Const'

ConstArg' : Const' → Ground BaseType'
ConstArg' zero = unitᵍ
ConstArg' succ = baseᵍ nat
ConstArg' plus = baseᵍ nat ×ᵍ baseᵍ nat

ConstResult' : Const' → Ground BaseType'
ConstResult' zero = baseᵍ nat
ConstResult' succ = baseᵍ nat
ConstResult' plus = baseᵍ nat


data ℂ' : Set where
  leaf : ℂ'
  node : ℂ'

par : ℂ' → Ground BaseType'
par leaf = unitᵍ
par node = baseᵍ nat

ar : ℂ' → Ground BaseType'
ar leaf = emptyᵍ
ar node = baseᵍ children

𝕊 : Signature.Signature
𝕊 = record
  { BaseType = BaseType'
  ; I = I'
  ; Const = Const'
  ; ConstArg = ConstArg'
  ; ConstResult = ConstResult'
  ; ℂ = ℂ'
  ; par = par
  ; ar = ar
  }



-- K : ∀ (c : Const') → ⟦ ConstArg' c ⟧ᵍ → ⟦ ConstResult' c ⟧ᵍ
-- K = ?

open import Interpreter 𝕊
open import STLC 𝕊

program : (x : ⊤) → ⊤
program = ⟦ unit ⟧ᵢ

program2 : (x : ⊤) → ℕ
program2 = ⟦ const zero unit ⟧ᵢ 
{-
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
                                  
program6 : ℕ
program6 = ⟦ fold (constr node 42 aux-tree) (λ { leaf → fun (fun (const 0))
                                               ; node → fun (fun ( var (∈-there ∈-here)))}) ⟧ᵢ tt 
                                                 -- app (var (base children ⇒ᵗ {!   !}) {{∈-here}}) (const left) ؛ (var (base nat) {{ ∈-there  {{∈-here}} }} ؛ app (var _ {{∈-here}}) (const right)))))}) ⟧ᵢ tt
  where
    aux-tree : Children → [] ⊢ tree
    aux-tree left = constr leaf tt λ { () }
    aux-tree right = constr node 9 λ { left → constr leaf tt λ { () }
                                     ; right → constr leaf tt λ { () } }


program7 : ⟦ ([] ∷ base nat) ∷ base nat ⟧ₑ → ℕ
program7 = ⟦ var (∈-there  ∈-here) ⟧ᵢ

program8 : ℕ
program8 = ⟦ var (∈-there (∈-there ∈-here)) ⟧ᵢ (((tt , 5) , 8) , 9)

program9 : (x : ⊤) (x₁ : ⟦ base nat ×ᵗ base nat ⟧) → ⟦ base nat ⟧
program9 = ⟦ fun (fst (var ∈-here)) ⟧ᵢ

program10 : ℕ
program10 = ⟦ app (fun (fst (var ∈-here))) ((const 5 ؛ const 4)) ⟧ᵢ tt

program11 : ℕ
program11 = ⟦ baseFun plus (const 5) (const 7) ⟧ᵢ tt

program12 : ℕ
program12 = ⟦
  fold
    (constr node 42 aux-tree)
    (λ { leaf → fun (fun (const 0))
       ; node → fun (fun (baseFun plus (var (∈-there ∈-here)) (baseFun plus (app (var ∈-here) (const left)) ((app (var ∈-here) (const right))))))}) ⟧ᵢ tt
  where
    aux-tree : Children → [] ⊢ tree
    aux-tree left = constr leaf tt λ { () }
    aux-tree right = constr node 9 λ { left → constr leaf tt λ { () }
                                     ; right → constr leaf tt λ { () } }
-}
{-
Vprasanja:
1. pri var bi lahko bil argument s tipom impliciten in bi se vedno delal? :)
2. prvi var bova mogla vedno podat here in there, da bo delal :) 
3. ali so te zadnji programi vredu napisani oz. ali je tko mislen al ne? :)
4. ali rabiva let ali ne → RABIVA 
5. kako sestet vse v drevesu - kako dodava plus

TODO:
1. probava ce dela var, kjer je argument s tipom impliciten
2. napiseva program s fold
-} 