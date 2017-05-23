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

{- examples -}

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

  φmono' : {c : A} (t u : 𝟚) (g : ⊤) .(d : δ {zero} c g) → φ {zero} {c} t g d ≡ φ {zero} {c} u g d → t ≡ u
  φmono' 𝟚.𝟘 𝟚.𝟘 g d eq = refl
  φmono' 𝟚.𝟘 𝟚.𝟙 g d ()
  φmono' 𝟚.𝟙 𝟚.𝟘 g d ()
  φmono' 𝟚.𝟙 𝟚.𝟙 g d eq = refl

  φmono : (c : A) (t u : 𝟚) → φ {zero} {c} t ≡ φ {zero} {c} u → t ≡ u
  φmono c t u pf = cong-iapp (cong-app pf tt) tt

  φepi : (c : A) → (b : (g : ⊤) → .(δ c g) → 𝟚) → ⊤ → Σ 𝟚 (λ a → φ {zero} {c} a ≡ b)
  φepi t u pf = (u tt tt) , refl

  θ : {n : ℕ} → 𝕏 (suc n) → 𝔻 𝕏 n → Bool
  θ {n} () g
  oc = MkOverChain (λ {n} {c} → φ {n} {c}) (λ {n} → θ {n})
  match : (n : ℕ) → MatchAt (VChain A) oc n
  match zero c = MkIsoFor (λ t → tt) (φmono c) (φepi c)
  match (suc n) ()
