module FuncCells2 where

open import Data.Nat
open import Data.Unit
open import Data.Bool
open import Data.Product
open import Relation.Binary.PropositionalEquality using (_≡_ ; subst ; sym)
open import Data.Empty
open import Data.Sum renaming ( _⊎_ to _⊕_ )
open import BoolUtil using (_≅_ ; _st_ ; 𝟚 ; IsoFor )
open _st_

𝔻 : ((n : ℕ) → Set) → (n : ℕ) → Set
𝔻 𝕏 zero = ⊤
𝔻 𝕏 (suc n) = 𝕏 n

record Chain : Set₁ where
  constructor MkChain
  field
    𝕏 : (n : ℕ) → Set
    δ : {n : ℕ} → 𝕏 n → 𝔻 𝕏 n → Set

module _OverChain (χ : Chain) where
  open Chain χ
  record OverChain : Set₁ where
    constructor MkOverChain
    field
      φ : {n : ℕ} {c : 𝕏 n} → 𝟚 → (g : 𝔻 𝕏 n) → .(δ c g) → 𝟚
      θ : {n : ℕ} → 𝕏 (suc n) → 𝔻 𝕏 n → Bool

open _OverChain

module FixChains (χ : Chain) (π : OverChain χ) where
  open Chain χ
  open OverChain π

  module Abbrevs (n : ℕ) where
    ℍ = 𝕏 (suc n)
    ℂ = 𝕏 n
    𝔾 = 𝔻 𝕏 n

  module SectionN {n : ℕ} where
    open Abbrevs n
    Section : ℂ → Set
    Section c = (g : 𝔾) → .(δ c g) → 𝟚
  open SectionN

  module FixN (n : ℕ) where
    open Abbrevs n
    record TwoHop (h : ℍ) (ν : Section h) (g : 𝔾) (g' : 𝟚) : Set where
      field
        c : ℂ
        .hop1 : δ h c
        .hop2 : δ c g
        .transport : φ (ν c hop1) g hop2  ≡ g'

    Calm : (h : ℍ) (ν : Section h) → Set
    Calm h ν = (g : 𝔾) (g' : 𝟚) → (if θ h g then ⊤ else ⊥) ≅ TwoHop h ν g g'

  module PredCalm where
    open FixN
    PredCalm : (n : ℕ) (c : 𝕏 n) (ν : Section c) → Set
    PredCalm zero c ν = ⊤
    PredCalm (suc n) c ν = Calm n c ν
  open PredCalm

  module FixN2 (n : ℕ) where
    open Abbrevs n
    MatchAt : Set
    MatchAt = (c : ℂ) → IsoFor φ (PredCalm n c)

  open FixN2 public

open FixChains

GoodChain : (χ : Chain) → Set₁
GoodChain χ = Σ (OverChain χ) (λ π → (n : ℕ) → MatchAt χ π n)
