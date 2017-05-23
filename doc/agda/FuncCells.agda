module FuncCells where

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
    δ : {n : ℕ} → 𝕏 n → 𝔻 𝕏 n → Set

module _OverChain (χ : Chain) where
  open Chain χ
  record OverChain : Set₁ where
    constructor MkOverChain
    field
      𝕧 : (n : ℕ) → Set -- this is "(-1)-indexed": e.g. 𝕧 0 lives over the ⊤ inserted by 𝔻
      p : {n : ℕ} → 𝕧 n → 𝔻 𝕏 n -- this type realizes the above comment
      φ : {n : ℕ} (v : 𝕧 (suc n)) {g : 𝔻 𝕏 n} (m : δ (p v) g) → 𝕧 n
      θ : {n : ℕ} → 𝕏 (suc n) → 𝔻 𝕏 n → Set

open _OverChain

module FixChains (χ : Chain) (π : OverChain χ) where
  open Chain χ
  open OverChain π

  Fiber : {n : ℕ} → (g : 𝔻 𝕏 n) (v : 𝕧 n)  → Set
  Fiber g v = p v ≡ g

  module SectionN {n : ℕ} where
    module Abbrevs where
      ℂ = 𝕏 n
      𝔾 = 𝔻 𝕏 n
      𝕘 = 𝕧 n
    open Abbrevs
    Section : ℂ → Set
    Section c = {g : 𝔾} → δ c g → 𝕘

    Sectional : {c : ℂ} → Section c → Set
    Sectional {c} σ = (g : 𝔾) (m : δ c g) → p (σ {g} m) ≡ g
  open SectionN hiding (module Abbrevs)

  module FixN (n : ℕ) where
    ℍ = 𝕏 (suc n)
    ℂ = 𝕏 n
    𝔾 = 𝔻 𝕏 n
    𝕘 = 𝕧 n
    𝕔 = 𝕧 (suc n)

    -- Section {suc n} h = (c : ℂ) → δ h c → 𝕔
    Calm : (h : ℍ) (ν : {c : ℂ} → δ h c → 𝕔) → Set
    Calm h ν = (g' : 𝕘) → θ h (p g') ≅ Σ ℂ (λ c → Σ (δ h c) (λ m₂ → Σ (δ (p (ν m₂)) (p g')) (λ m₁ → φ (ν m₂) m₁ ≡ g')))

  module PredCalm where
    open FixN
    PredCalm : (n : ℕ) (c : 𝕏 n) (ν : Section c) → Set
    PredCalm zero c ν = ⊤
    PredCalm (suc n) c ν = Calm n c ν
  open PredCalm

  module FixN2 (n : ℕ) where
    open FixN n public

    GoodFunc : (c : ℂ) (ν : Section c)  → Set
    GoodFunc c ν = Sectional ν × PredCalm n c ν

    Match : (c : ℂ) → Set
    Match c = (𝕔 st (Fiber c) ≅ (Section c) st (GoodFunc c))

    {- the isomoprhism in m preserves the fibered set morphism φ -}
    PresRel : (c : ℂ) → Match c → Set
    PresRel c M = (c' : 𝕔 st Fiber c) (g : 𝔾) (m : δ c g) → PresRelAt c' g m
      where
      PresRelAt : (c' : 𝕔 st Fiber c) (g : 𝔾) (m : δ c g) → Set
      PresRelAt c' g m = Item (proj₁ M c') m ≡ φ (Item c') coe-m
        where
        coe-m : δ (p (Item c')) g
        coe-m = isubst (λ x → δ x g) (sym (Pf c')) m

    record GoodAtN : Set where
      field
        AllMatch : (c : ℂ) → Σ (Match c) (PresRel c)
        AllDouble : (g : 𝔾) → 𝕘 st (Fiber g) ≅ 𝟚
        AllSingle : (h : ℍ) (g : 𝔾) → θ h g ≅ ⊥ ⊕ θ h g ≅ ⊤
        Goodφ : (c' : 𝕔) (g : 𝔾) (m : δ (p c') g) → Fiber g (φ c' m)

  open FixN2 public using ( GoodAtN )

open FixChains

GoodChain : (χ : Chain) → Set₁
GoodChain χ = Σ (OverChain χ) (λ π → (n : ℕ) → GoodAtN χ π n)
