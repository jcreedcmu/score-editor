module ChainCells (A : Set) where

-- open import Level renaming (suc to lsuc) hiding (zero)
open import Data.Integer renaming (suc to isuc ; _+_ to _i+_ ; _*_ to _i*_ ) hiding ( _⊔_ )
open import Data.Nat hiding ( _⊔_ )
open import Data.Unit
open import Data.Empty
open import Data.Bool
open import Data.Sum renaming ( _⊎_ to _⊕_ )
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


one : (B : Set) → (B → Bool) → Set
one B pred = Σ B (λ b → (pred b ≡ true) × ((b' : B) → pred b' ≡ true → b ≡ b'))

none : (B : Set) → (B → Bool) → Set
none B pred = (b : B) → pred b ≡ false

balanced : {B : Set} → (B → Tern) → Set
balanced {B} f = one B (λ b → Tern= (f b) t+) ×
                 one B (λ b → Tern= (f b) t-)

null : {B : Set} → (B → Tern) → Set
null {B} f = none B (λ b → Tern= (f b) t+) ×
             none B (λ b → Tern= (f b) t-)

calm : {B : Set} → (B → Tern) → Set
calm {B} f = balanced f ⊕ null f

record Chain : Set₁ where
  constructor MkChain
  field
    ℂ : ℕ → Set
    δ : (n : ℕ) →  ℂ (suc n) → ℂ n → Tern

isZeroCover : (χ : Chain) (n : ℕ) → (Chain.ℂ χ n → Tern) → Set
isZeroCover (MkChain ℂ δ) zero v = balanced v
isZeroCover (MkChain ℂ δ) (suc n) v = (c : ℂ n) → calm (λ e → v e ** δ n e c)

GoodCell : {n : ℕ} (χ : Chain) (c : Chain.ℂ χ (suc n)) → Set
GoodCell {n} χ@(MkChain ℂ δ) c = isZeroCover χ n (δ n c)

Good : Chain → Set
Good χ@(MkChain ℂ δ) = (n : ℕ) (c : ℂ (suc n)) → GoodCell χ c
