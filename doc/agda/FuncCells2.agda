module FuncCells2 where

open import Data.Nat
open import Data.Unit
open import Data.Product
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.Empty
open import Data.Sum renaming ( _⊎_ to _⊕_ )
open import BoolUtil using (_≅_ ; _st_ ; IsoFor ; MkIsoFor )
open _st_

𝔻 : ((n : ℕ) → Set) → (n : ℕ) → Set
𝔻 𝕏 0 = ⊥
𝔻 𝕏 1 = ⊤
𝔻 𝕏 (suc (suc n)) = 𝕏 n

record Chain : Set₁ where
  constructor MkChain
  field
    𝕏 : (n : ℕ) → Set
    δ : (n : ℕ) → 𝔻 𝕏 (suc n) → 𝔻 𝕏 n  → Set
  𝕐 : (n : ℕ) → Set
  𝕐 n = 𝔻 𝕏 n

module _OverChain (χ : Chain) where
  open Chain χ
  record OverChain : Set₁ where
    constructor MkOverChain
    field
      F : Set -- fiber
      φ : {n : ℕ} {g : 𝕐 (suc n)} → F → (z : 𝕐 n) → δ n g z → F
      θ : {n : ℕ} → 𝕏 n → 𝕐 n → Set

open _OverChain public

module Fix (χ : Chain) (π : OverChain χ) (n : ℕ) where
  open Chain χ
  open OverChain π
  ℂ = 𝕐 (suc (suc n))
  𝔾 = 𝕐 (suc n)
  ℤ = 𝕐 n
  Section : (c : ℂ) → Set
  Section c = (g : 𝔾) → δ (suc n) c g → F
  record TwoHop (c : ℂ) (ν : Section c) (z : ℤ) (z' : F) : Set where
    field
      g : 𝔾
      hop1 : δ (suc n) c g
      hop2 : δ n g z
      transport : φ (ν g hop1) z hop2 ≡ z'
  Calm : (c : ℂ) → Section c → Set
  Calm c ν = (z : ℤ) (z' : F) → θ c z ≅ TwoHop c ν z z'
  MatchAt : Set
  MatchAt = (c : ℂ) → IsoFor φ (Calm c)

GoodChain : (χ : Chain) → Set₁
GoodChain χ = Σ (OverChain χ) (λ π → (n : ℕ) → Fix.MatchAt χ π n)
