module FuncCells2 where

open import Data.Nat
open import Data.Unit
open import Data.Bool
open import Data.Product
open import Relation.Binary.PropositionalEquality using (_≡_ ; subst ; sym)
open import Data.Empty
open import Data.Sum renaming ( _⊎_ to _⊕_ )
open import BoolUtil using (_≅_ ; _st_ ; 𝟚 ; isubst )
open _st_

𝔻 : ((n : ℕ) → Set) → (n : ℕ) → Set
𝔻 𝕏 zero = ⊤
𝔻 𝕏 (suc n) = 𝕏 n

record Chain : Set₁ where
  constructor MkChain
  field
    𝕏 : (n : ℕ) → Set
    ∂ : {n : ℕ} → 𝕏 n → 𝔻 𝕏 n → Bool

  δ : {n : ℕ} → 𝕏 n → 𝔻 𝕏 n → Set
  δ c g = ∂ c g ≡ true

module _OverChain (χ : Chain) where
  open Chain χ
  record OverChain : Set₁ where
    constructor MkOverChain
    field
      φ : {n : ℕ} {c : 𝕏 n} (g : 𝔻 𝕏 n) → .(δ c g) → 𝟚 → 𝟚
      θ : {n : ℕ} → 𝕏 (suc n) → 𝔻 𝕏 n → Set

open _OverChain

module FixChains (χ : Chain) (π : OverChain χ) where
  open Chain χ
  open OverChain π

  module SectionN {n : ℕ} where
    module Abbrevs where
      ℂ = 𝕏 n
      𝔾 = 𝔻 𝕏 n
    open Abbrevs
    Section : ℂ → Set
    Section c = (g : 𝔾) → .(δ c g) → 𝟚
  open SectionN hiding (module Abbrevs)

  module FixN (n : ℕ) where
    ℍ = 𝕏 (suc n)
    ℂ = 𝕏 n
    𝔾 = 𝔻 𝕏 n

    record TwoHop (h : ℍ) (ν : Section h) (g : 𝔾) (g' : 𝟚) : Set where
      field
        c : ℂ
        .hop1 : δ h c
        .hop2 : δ c g
        .transport : φ g hop2 (ν c hop1) ≡ g'

    Calm : (h : ℍ) (ν : Section h) → Set
    Calm h ν = (g : 𝔾) (g' : 𝟚) → θ h g ≅ TwoHop h ν g g'

  module PredCalm where
    open FixN
    PredCalm : (n : ℕ) (c : 𝕏 n) (ν : Section c) → Set
    PredCalm zero c ν = ⊤
    PredCalm (suc n) c ν = Calm n c ν
  open PredCalm

  module FixN2 (n : ℕ) where
    open FixN n public

    Match : (c : ℂ) → Set
    Match c = 𝟚 ≅ (Section c) st (PredCalm n c)

    PresRel : (c : ℂ) → Match c → Set
    PresRel c M = (c' : 𝟚) (g : 𝔾) .(m : δ c g) → Item (proj₁ M c') g m ≡ φ g m c'

    record GoodAtN : Set where
      field
        AllMatch : (c : ℂ) → Σ (Match c) (PresRel c)
        AllSingle : (h : ℍ) (g : 𝔾) → θ h g ≅ ⊥ ⊕ θ h g ≅ ⊤

  open FixN2 public using ( GoodAtN )

open FixChains

GoodChain : (χ : Chain) → Set₁
GoodChain χ = Σ (OverChain χ) (λ π → (n : ℕ) → GoodAtN χ π n)
