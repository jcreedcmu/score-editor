module BoolCells where

open import Data.Nat
open import Data.Unit
open import Data.Bool
open import Data.Product
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; subst; sym)
open import Data.Sum renaming ( _⊎_ to _⊕_ )
open import BoolUtil

{- Surely don't need *all* of these... --------}
Size2 : (B : Set) → Set
Size2 B = Σ B (λ b₁ → Σ B (λ b₂ →
  b₁ ≢ b₂ × ((b : B) → b ≡ b₁ ⊕ b ≡ b₂)))

Size2f : (B : Set) → Set
Size2f B = Σ (Bool → B) (λ f →
  f true ≢ f false
  × ((b : B) → b ≡ f true ⊕ b ≡ f false))

2niq : (B : Set) → (B → Set) → Set
2niq B pred = Σ B (λ b₁ → Σ B (λ b₂ →
  b₁ ≢ b₂
  × pred b₁
  × pred b₂
  × ((b : B) → pred b → b ≡ b₁ ⊕ b ≡ b₂)))

2niqf : (B : Set) → (B → Set) → Set
2niqf B pred = Σ (Bool → B) (λ f →
  f true ≢ f false
  × pred (f true)
  × pred (f false)
  × ((b : B) → pred b → b ≡ f true ⊕ b ≡ f false))
{---------}

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
  Duple : (n : ℕ) (k : 𝕏 n → Bool) → Set
  Duple n k = {!!}
  GoodFunc n v = {!!}

  module FixN (n : ℕ) where
    ℍ = 𝕏 (suc n)
    ℂ = 𝕏 n
    𝔾 = 𝔻 𝕏 n


    GoodCells : Set
    GoodCells = (h : ℍ) → GoodFunc n (δ h)
