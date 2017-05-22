module BoolCells where

open import Data.Nat
open import Data.Unit
open import Data.Bool
open import Data.Product
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.Empty
open import Data.Sum renaming ( _⊎_ to _⊕_ )
open import BoolUtil hiding (Calm)

𝔻 : ((n : ℕ) → Set) → (n : ℕ) → Set
𝔻 𝕏 zero = ⊤
𝔻 𝕏 (suc n) = 𝕏 n

record Chain : Set₁ where
  constructor MkChain
  field
    𝕏 : (n : ℕ) → Set
    δ : {n : ℕ} → 𝕏 n → 𝔻 𝕏 n → Bool

module _OverChain (χ : Chain) where
  open Chain χ
  record OverChain : Set₁ where
    constructor MkOverChain
    field
      𝕧 : (n : ℕ) → Set -- this is "(-1)-indexed": e.g. 𝕧 0 lives over the ⊤ inserted by 𝔻
      p : {n : ℕ} → 𝕧 n → 𝔻 𝕏 n -- this type realizes the above comment
      ∂ : {n : ℕ} → 𝕧 (suc n) → 𝕧 n → Bool
open _OverChain

module FixChains (χ : Chain) (π : OverChain χ) where
  open Chain χ
  open OverChain π

  Fiber : {n : ℕ} → (g : 𝔻 𝕏 n) (v : 𝕧 n)  → Set
  Fiber g v = p v ≡ g

  module FixN (n : ℕ) where
    ℂ = 𝕏 n
    𝔾 = 𝔻 𝕏 n
    𝕘 = 𝕧 n
    𝕔 = 𝕧 (suc n)

    Sectional : (c : ℂ) (ν : 𝕘 → Bool) → Set
    Sectional c ν = (g : 𝔾) → (if δ c g then ⊤ else ⊥) ≅ (𝕘 st (λ g' → Fiber g g' × (ν g' ≡ true)))

    WholeFiber : ((B : Set) → (B → Bool) → Set) → (g : 𝔾) (ν : 𝕔 → Bool) → Set
    WholeFiber cond g ν = (g' : 𝕘) → Fiber g g' → cond 𝕔 (λ c' → ν c' ∧ ∂ c' g')

    Calm : (ν : 𝕔 → Bool) → Set
    Calm ν = (g : 𝔾) → WholeFiber Uniq g ν ⊕ WholeFiber None g ν

  module PredCalm where
    open FixN
    PredCalm : (n : ℕ) (ν : 𝕧 n → Bool) → Set
    PredCalm zero ν = ⊤
    PredCalm (suc n) ν = Calm n ν
  open PredCalm

  module FixN2 (n : ℕ) where
    open FixN n public
    GoodFunc : (c : ℂ) (ν : 𝕘 → Bool)  → Set
    GoodFunc c ν = Sectional c ν × PredCalm n ν

    AllMatch : Set
    AllMatch = (c : ℂ) → Σ (𝕔 st (Fiber c) ≅ (𝕘 → Bool) st (GoodFunc c))
      (λ f → (g' : 𝕘) (c' : 𝕔 st Fiber c) → Item (proj₁ f c') g' ≡ ∂ (Item c') g') {- this isomorphism agrees with ∂ -}

    AllDouble : Set
    AllDouble = (g : 𝔾) → 𝟚 ≅ 𝕘 st (Fiber g)

  open FixN2

  Good∂ : Set
  Good∂ = {n : ℕ} (v₁ : 𝕧 (suc n)) (v₂ : 𝕧 n) → ∂ v₁ v₂ ≡ true → δ (p v₁) (p v₂) ≡ true

  GoodOverChain : Set
  GoodOverChain = ((n : ℕ) → AllMatch n × AllDouble n) × Good∂

open FixChains

GoodChain : (χ : Chain) → Set₁
GoodChain χ = Σ (OverChain χ) (λ π → GoodOverChain χ π)
