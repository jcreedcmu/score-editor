module BoolCells where

open import Data.Nat
open import Data.Unit
open import Data.Bool
open import Data.Product
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; subst; sym; cong; trans)
open import Data.Sum renaming ( _⊎_ to _⊕_ )
open import BoolUtil

data 𝟚 : Set where
  𝟘 : 𝟚
  𝟙 : 𝟚

Epi : {A B : Set} → (A → B) → Set
Epi {A} {B} f = (b : B) → Σ A (λ a → f a ≡ b)

Mono : {A B : Set} → (A → B) → Set
Mono {A} {B} f = (a₁ a₂ : A) → f a₁ ≡ f a₂ → a₁ ≡ a₂

_⊚_ : {A : Set} {a b c : A} → a ≡ b → b ≡ c → a ≡ c
p ⊚ q = trans p q
infixr 20 _⊚_

_≅_ : (A B : Set) → Set
A ≅ B = Σ (A → B) (λ f → Epi f × Mono f)

≅sym : {A B : Set} → A ≅ B → B ≅ A
≅sym {A} {B} (f , (e , m)) = (λ b → proj₁ (e b)) , epiPf , monoPf where
  epiPf : (a : A) → Σ B (λ v → proj₁ (e v) ≡ a)
  epiPf = (λ a → (f a) , (m (proj₁ (e (f a))) a (proj₂ (e (f a)))))
  monoPf : Mono (λ b → proj₁ (e b))
  monoPf = λ a₁ a₂ eq → sym (proj₂ (e a₁)) ⊚ cong f eq ⊚ (proj₂ (e a₂))

Doubleton : (B : Set) → Set
Doubleton B = 𝟚 ≅ B

2niq : (B : Set) → (B → Set) → Set
2niq B pred = Doubleton (B st pred)

𝔻 : ((n : ℕ) → Set) → (n : ℕ) → Set
𝔻 𝕏 zero = ⊤
𝔻 𝕏 (suc n) = 𝕏 n

record Chain : Set₁ where
  constructor MkChain
  field
    𝕏 : (n : ℕ) → Set
    δ : {n : ℕ} → 𝕏 n → 𝔻 𝕏 n → Bool

module FixChain (χ : Chain) where
  𝕏 = Chain.𝕏 χ
  δ = Chain.δ χ

  GoodFunc : (n : ℕ) → (𝕏 n → Bool) → Set


  Signing : (n : ℕ) (v : 𝕏 n → Bool) → Set
  Signing n v = (c : 𝕏 n st (λ c → v c ≡ true)) → 𝟚

  GoodSigning : (n : ℕ) (v : 𝕏 n → Bool) → Signing n v → Set
  GoodSigning = {!!}


  GoodFunc n v = 2niq (Signing n v) (GoodSigning n v)

  module FixN (n : ℕ) where
    ℍ = 𝕏 (suc n)
    ℂ = 𝕏 n
    𝔾 = 𝔻 𝕏 n


    GoodCells : Set
    GoodCells = (h : ℍ) → GoodFunc n (δ h)
