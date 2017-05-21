module ChainCells (A : Set) where

-- open import Level renaming (suc to lsuc) hiding (zero)
open import Data.Integer renaming (suc to isuc ; _+_ to _i+_ ; _*_ to _i*_ ) hiding ( _⊔_ )
open import Data.Nat hiding ( _⊔_ )
open import Data.Unit
open import Data.Empty
open import Data.Bool
open import Data.Sum
open import Data.Product
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Level hiding ( zero ) renaming (suc to lsuc)
open import Function
open import Data.Fin hiding (_+_ ; #_)

data Tern : Set where
 t+ : Tern
 t- : Tern
 t0 : Tern

Tern= : Tern → Tern → Bool
Tern= t+ t+ = true
Tern= t- t- = true
Tern= t0 t0 = true
Tern= _ _ = false

_**_ : Tern -> Tern -> Tern
t0 ** _ = t0
_ ** t0 = t0
t+ ** x = x
x ** t+ = x
t- ** t- = t+

record Oper (B : Set) : Set₁ where
  constructor MkOper
  field
    φ : (A : Set) → (B → A → A) → A → A
    all : (B → Bool) → Bool
    one : (B → Bool) → Bool

balanced : {B : Set} → (Oper B) → (B → Tern) → Set
balanced ω f = (Oper.one ω (λ b → Tern= (f b) t+) ∧
               Oper.one ω (λ b → Tern= (f b) t-)) ≡ true

record Chain : Set₁ where
  constructor MkChain
  field
    ℂ : ℕ → Set
    ω : (n : ℕ) → Oper (ℂ n)
    δ : (n : ℕ) →  ℂ (suc n) → ℂ n → Tern

UniqueScanner : Set → Set
UniqueScanner A = (A → Bool) → Bool

-- all : (n : ℕ) → (Fin n → Bool) → Bool
-- all zero pred = true
-- all (suc n) pred = pred zero ∧ all n (pred ∘ suc)

-- sum : (n : ℕ) → (Fin n → ℕ) → ℕ
-- sum zero f = zero
-- sum (suc n) f = f zero + sum n (f ∘ suc)

ffold : (A : Set) (n : ℕ) → (Fin n → A → A) → A → A
ffold A zero f x = x
ffold A (suc n) f x = f zero (ffold A n (f ∘ suc) x)

sum : (n : ℕ) → (Fin n → ℕ) → ℕ
sum n f = ffold ℕ n (λ m acc → acc + f m) 0


-- FUS : (n : ℕ) → UniqueScanner (Fin n)
-- FUS n pred = {!!}

isZeroCover : (χ : Chain) (n : ℕ) → (Chain.ℂ χ n → Tern) → Set
isZeroCover (MkChain ℂ ω δ) zero v = balanced (ω zero) v
isZeroCover (MkChain ℂ ω δ) (suc n) v = (c : ℂ n) → balanced (ω (suc n)) (λ e → v e ** δ n e c)

GoodCell : {n : ℕ} (χ : Chain) (c : Chain.ℂ χ (suc n)) → Set
GoodCell {n} χ@(MkChain ℂ ω δ) c = isZeroCover χ n (δ n c)

Good : Chain → Set
Good χ@(MkChain ℂ ω δ) = (n : ℕ) (c : ℂ (suc n)) → GoodCell χ c
