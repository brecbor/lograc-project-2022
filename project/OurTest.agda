open import Signature

module OurTest where


open import Data.Unit using (⊤; tt)
open import Data.Empty
open import Data.Nat
open import Data.Product
open import Data.Sum
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; subst)
open import Function using (id; _∘_)
open import Data.Bool

data BaseType' : Set where
  nat : BaseType'
  bool : BaseType'

I' : BaseType' → Set
I' nat = ℕ
I' bool = Bool

data Const' : Set where
  zero : Const'
  succ : Const'
  plus : Const'
  true : Const'
  false : Const'
  if-then-else : {Ground BaseType'} → Const'

ConstArg' : Const' → Ground BaseType'
ConstArg' zero = unitᵍ
ConstArg' succ = baseᵍ nat
ConstArg' plus = baseᵍ nat ×ᵍ baseᵍ nat
ConstArg' true = unitᵍ
ConstArg' false = unitᵍ
ConstArg' (if-then-else {A}) = baseᵍ bool ×ᵍ (A ×ᵍ A)

ConstResult' : Const' → Ground BaseType'
ConstResult' zero = baseᵍ nat
ConstResult' succ = baseᵍ nat
ConstResult' plus = baseᵍ nat
ConstResult' true = baseᵍ bool
ConstResult' false = baseᵍ bool
ConstResult' (if-then-else {A}) = A

data ℂ' : Set where
  leaf : ℂ'
  node : ℂ'

par' : ℂ' → Ground BaseType'
par' leaf = unitᵍ
par' node = baseᵍ nat

ar' : ℂ' → Ground BaseType'
ar' leaf = emptyᵍ
ar' node = unitᵍ +ᵍ unitᵍ

𝕊 : LangSignature
𝕊 = record
  { BaseType = BaseType'
  ; Const = Const'
  ; ConstArg = ConstArg'
  ; ConstResult = ConstResult'
  ; ℂ = ℂ'
  ; par = par'
  ; ar = ar'
  }

open LangSignature 𝕊

open import STLC 𝕊
open import Interpreter 𝕊 I' 

K : (c : Const) → ⟦ ConstArg c ⟧ᵍ → ⟦ ConstResult c ⟧ᵍ
K zero tt = 0
K succ n = 1 + n
K plus (m , n) = m + n
K true tt = true
K false tt = false
K if-then-else (b , e₁ , e₂) = if b then e₁ else e₂

-- helper function so that we can use (` 5) instead of (succ (succ ...)) in our programs
infix 20 `_ 
`_ : {Γ : Ctx} → ℕ → Γ ⊢ base nat
` zero = const zero unit
` suc x = const succ (` x)


open LangInterpretation K 


program : (x : ⊤) → ⊤
program = ⟦ unit ⟧ᵢ

program2 : (x : ⊤) → ℕ
program2 = ⟦ ` 1 ⟧ᵢ

program3 : ℕ
program3 = ⟦ const zero unit ⟧ᵢ tt

program4 : Σ ℕ (λ _ → ℕ)
program4 = ⟦ LET const succ (const succ (const zero unit)) IN
               var ∈-here ؛ const zero unit ⟧ᵢ tt

program5 : ℕ
program5 = ⟦ fst (const succ (const succ (const zero unit)) ؛ const zero unit) ⟧ᵢ tt

-- plus
program6 : ℕ
program6 = ⟦ const plus (` 42 ؛ ` 9) ⟧ᵢ tt

-- if-then-else
program7 : (x : Σ ⊤ (λ _ → Bool)) → ℕ
program7 = ⟦ const if-then-else (var ∈-here ؛ const succ (const zero unit) ؛ const zero unit) ⟧ᵢ
-- program7 (tt , true)  --->  1

-- case
program8 : Σ Bool (λ _ → ℕ)
program8 = ⟦ case (inr (const zero unit)) (const false unit ؛ var ∈-here) (const true unit ؛ var ∈-here) ⟧ᵢ tt

-- leaf
program9 : Tree (⟦_⟧ᵍ ∘ par) (⟦_⟧ᵍ ∘ ar)
program9 = ⟦ constr leaf unit (absurd (var ∈-here)) ⟧ᵢ tt

-- node
program10 : Tree (⟦_⟧ᵍ ∘ par) (⟦_⟧ᵍ ∘ ar)
program10 = ⟦ LET constr leaf unit (absurd (var ∈-here)) IN
              constr node (` 42)
                          (var (∈-there ∈-here)) ⟧ᵢ tt

-- node and case
program11 : Tree (⟦_⟧ᵍ ∘ par) (⟦_⟧ᵍ ∘ ar)
program11 = ⟦ LET constr leaf unit (absurd (var ∈-here)) IN
                 constr node
                   (` 42)
                   (case (var ∈-here) 
                      (var (∈-there (∈-there ∈-here)))
                      (var (∈-there (∈-there ∈-here)))) ⟧ᵢ tt

-- tree with 2 nodes that is used in next programs
binary_tree : [] ⊢ tree
binary_tree = LET constr leaf unit (absurd (var ∈-here)) IN
               LET constr node
                    (` 42)
                    (var (∈-there ∈-here))
                IN constr node
                     (` 9)
                     (case (var ∈-here)
                        (var (∈-there (∈-there ∈-here)))
                        (var (∈-there (∈-there (∈-there ∈-here)))))

-- interpretation of binary_tree
program12 : Tree (⟦_⟧ᵍ ∘ par) (⟦_⟧ᵍ ∘ ar)
program12 = ⟦ binary_tree ⟧ᵢ tt

-- sum values of nodes in binary_tree                        
program13 : ℕ
program13 = ⟦ fold (λ { leaf → const zero unit
                     ; node → const plus 
                                (var (∈-there ∈-here) 
                                ؛ const plus 
                                    (app (var ∈-here) (inl unit) 
                                    ؛ app (var ∈-here) (inr unit)))}) 
                  binary_tree ⟧ᵢ tt 

proof13 : program13 ≡ 51
proof13 = refl                  

program14 : ⟦ ([] ∷ base nat) ∷ base nat ⟧ₑ → ℕ
program14 = ⟦ var (∈-there  ∈-here) ⟧ᵢ

program15 : ℕ
program15 = ⟦ var (∈-there (∈-there ∈-here)) ⟧ᵢ (((tt , 5) , 8) , 9)

program16 : (x : ⊤) (x₁ : ⟦ base nat ×ᵗ base nat ⟧) → ⟦ base nat ⟧
program16 = ⟦ fun (fst (var ∈-here)) ⟧ᵢ

