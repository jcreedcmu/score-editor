module SetCells where

open import Data.Nat
open import Data.Unit
open import Data.Bool
open import Data.Product
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.Empty
open import Data.Sum renaming ( _⊎_ to _⊕_ )
open import BoolUtil using (_≅_ ; _st_ ; 𝟚 )
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
      ∂ : {n : ℕ} → 𝕧 (suc n) → 𝕧 n → Set
      θ : {n : ℕ} → 𝕏 (suc n) → 𝔻 𝕏 n → Set

open _OverChain

module FixChains (χ : Chain) (π : OverChain χ) where
  open Chain χ
  open OverChain π

  Fiber : {n : ℕ} → (g : 𝔻 𝕏 n) (v : 𝕧 n)  → Set
  Fiber g v = p v ≡ g

  module FixN (n : ℕ) where
    ℍ = 𝕏 (suc n)
    ℂ = 𝕏 n
    𝔾 = 𝔻 𝕏 n
    𝕘 = 𝕧 n
    𝕔 = 𝕧 (suc n)

    Sectional : (c : ℂ) (ν : 𝕘 → Set) → Set
    Sectional c ν = (g : 𝔾) → δ c g ≅ Σ 𝕘 (λ g' → Fiber g g' × ν g')

    Calm : (h : ℍ) (ν : 𝕔 → Set) → Set
    Calm h ν = (g' : 𝕘) → θ h (p g') ≅ Σ 𝕔 (λ c' → ∂ c' g' × ν c')

  module PredCalm where
    open FixN
    PredCalm : (n : ℕ) (c : 𝕏 n) (ν : 𝕧 n → Set) → Set
    PredCalm zero c ν = ⊤
    PredCalm (suc n) c ν = Calm n c ν
  open PredCalm

  module FixN2 (n : ℕ) where
    open FixN n public
    GoodFunc : (c : ℂ) (ν : 𝕘 → Set)  → Set
    GoodFunc c ν = Sectional c ν × PredCalm n c ν

    Match : (c : ℂ) → Set₁
    Match c = (𝕔 st (Fiber c) ≅ (𝕘 → Set) st (GoodFunc c))

    {- the isomoprhism in m preserves the 'relation' ∂ -}
    PresRel : (c : ℂ) → Match c → Set₁
    PresRel c m =  (c' : 𝕔 st Fiber c) (g' : 𝕘) → Item (proj₁ m c') g' ≡ ∂ (Item c') g'

    AllMatch : Set₁
    AllMatch = (c : ℂ) → Σ (Match c) (PresRel c)

    AllDouble : Set
    AllDouble = (g : 𝔾) → 𝟚 ≅ 𝕘 st (Fiber g)

    AllSingle : Set
    AllSingle = (h : ℍ) (g : 𝔾) → θ h g ≅ ⊥ ⊕ θ h g ≅ ⊤

  open FixN2

  Good∂ : Set
  Good∂ = {n : ℕ} (v₁ : 𝕧 (suc n)) (v₂ : 𝕧 n) → ∂ v₁ v₂ → δ (p v₁) (p v₂)

  GoodOverChain : Set₁
  GoodOverChain = ((n : ℕ) → AllMatch n × AllDouble n × AllSingle n) × Good∂

open FixChains

GoodChain : (χ : Chain) → Set₁
GoodChain χ = Σ (OverChain χ) (λ π → GoodOverChain χ π)
