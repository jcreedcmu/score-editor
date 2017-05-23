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

module FixChains (χ : Chain) (π : OverChain χ) where
  open Chain χ
  open OverChain π

  module Abbrevs (n : ℕ) where
    ℂ = 𝕐 (suc (suc n))
    𝔾 = 𝕐 (suc n)
    ℤ = 𝕐 n
    Δcg = λ c g → δ {suc n} c g
    Δgz = λ g z → δ {n} g z

  module FixN (n : ℕ) where
    open Abbrevs n

    Section : ℂ → Set
    Section c = (g : 𝔾) → .(Δcg c g) → 𝟚

    record TwoHop (c : ℂ) (ν : Section c) (z : ℤ) (z' : 𝟚) : Set where
      field
        g : 𝔾
        .hop1 : Δcg c g
        .hop2 : Δgz g z
        .transport : φ (ν g hop1) z hop2 ≡ z'

    Calm : (c : ℂ) (ν : Section c) → Set
    Calm c ν = (z : ℤ) (z' : 𝟚) → (if θ c z then ⊤ else ⊥) ≅ TwoHop c ν z z'

    MatchAt : Set
    MatchAt = (c : ℂ) → IsoFor φ (Calm c)
  open FixN public using ( MatchAt )
open FixChains

GoodChain : (χ : Chain) → Set₁
GoodChain χ = Σ (OverChain χ) (λ π → (n : ℕ) → MatchAt χ π n)

{- obsolete examples -}
{-
0Chain : Chain
0Chain = MkChain 𝕏 (λ {n} → δ {n}) where
  𝕏 : (n : ℕ) → Set
  𝕏 n = ⊥
  δ : {n : ℕ} → 𝕏 n → 𝔻 𝕏 n → Set
  δ () y

0GoodChain : GoodChain 0Chain
0GoodChain = oc , match where
  open Chain 0Chain
  φ : {n : ℕ} {c : 𝕏 n} → 𝟚 → (g : 𝔻 𝕏 n) → .(δ c g) → 𝟚
  φ {n} {()} t g d
  θ : {n : ℕ} → 𝕏 (suc n) → 𝔻 𝕏 n → Bool
  θ {n} () g
  oc = MkOverChain (λ {n} → φ {n}) (λ {n} → θ {n})
  match : (n : ℕ) → MatchAt 0Chain oc n
  match n ()

VChain : (A : Set) → Chain
VChain A = MkChain 𝕏 (λ {n} → δ {n}) where
  𝕏 : (n : ℕ) → Set
  𝕏 0 = A
  𝕏 (suc n) = ⊥
  δ : {n : ℕ} → 𝕏 n → 𝔻 𝕏 n → Set
  δ {0} c tt = ⊤
  δ {suc n} () g

VGoodChain : (A : Set) → GoodChain (VChain A)
VGoodChain A = oc , match where
  open Chain (VChain A)
  φ : {n : ℕ} {c : 𝕏 n} → 𝟚 → (g : 𝔻 𝕏 n) → .(δ c g) → 𝟚
  φ {zero} {c} t tt d = t
  φ {suc n} {()} t g d

  φmono : (c : A) (t u : 𝟚) → (λ g .d → t) ≡ (λ g .d → u) → t ≡ u
  φmono c t u pf = cong-iapp (cong-app pf tt) tt

  φepi : (c : A) → (b : (g : ⊤) → .(δ c g) → 𝟚) → ⊤ → Σ 𝟚 (λ a → (λ g .d → a) ≡ b)
  φepi c u tt = (u tt tt) , refl

  θ : {n : ℕ} → 𝕏 (suc n) → 𝔻 𝕏 n → Bool
  θ {n} () g
  oc = MkOverChain (λ {n} {c} → φ {n} {c}) (λ {n} → θ {n})
  match : (n : ℕ) → MatchAt (VChain A) oc n
  match zero c = MkIsoFor (λ t → tt) (φmono c) (φepi c)
  match (suc n) ()
-}
