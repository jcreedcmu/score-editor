module FuncCells2 where

open import Data.Nat
open import Data.Unit
open import Data.Bool
open import Data.Product
open import Relation.Binary.PropositionalEquality using (_≡_ ; subst ; sym ; cong-app ; refl)
open import Data.Empty
open import Data.Sum renaming ( _⊎_ to _⊕_ )
open import BoolUtil using (_≅_ ; _st_ ; 𝟚 ; IsoFor ; MkIsoFor ; cong-iapp )
open _st_

𝔻 : ((n : ℕ) → Set) → (n : ℕ) → Set
𝔻 𝕏 0 = ⊥
𝔻 𝕏 1 = ⊤
𝔻 𝕏 (suc (suc n)) = 𝕏 n

record Chain : Set₁ where
  constructor MkChain
  field
    𝕏 : (n : ℕ) → Set
    δ : {n : ℕ} → 𝔻 𝕏 (suc n) → 𝔻 𝕏 n  → Set
  𝕐 : (n : ℕ) → Set
  𝕐 n = 𝔻 𝕏 n

module _OverChain (χ : Chain) where
  open Chain χ
  record OverChain : Set₁ where
    constructor MkOverChain
    field
      φ : {n : ℕ} {g : 𝕐 (suc n)} → 𝟚 → (z : 𝕐 n) → .(δ {n} g z) → 𝟚
      θ : {n : ℕ} → 𝕏 n → 𝕐 n → Bool

open _OverChain

module Fix (χ : Chain) (π : OverChain χ) (n : ℕ) where
  open Chain χ
  open OverChain π
  ℂ = 𝕐 (suc (suc n))
  𝔾 = 𝕐 (suc n)
  ℤ = 𝕐 n
  Δcg = λ c g → δ {suc n} c g
  Δgz = λ g z → δ {n} g z
  record TwoHop (c : ℂ) (ν : (g : 𝔾) → .(Δcg c g) → 𝟚) (z : ℤ) (z' : 𝟚) : Set where
    field
      g : 𝔾
      .hop1 : Δcg c g
      .hop2 : Δgz g z
      .transport : φ (ν g hop1) z hop2 ≡ z'
  MatchAt : Set
  MatchAt = (c : ℂ) → IsoFor φ (λ ν → (z : ℤ) (z' : 𝟚) → (if θ c z then ⊤ else ⊥) ≅ TwoHop c ν z z')
open Fix

GoodChain : (χ : Chain) → Set₁
GoodChain χ = Σ (OverChain χ) (λ π → (n : ℕ) → MatchAt χ π n)
