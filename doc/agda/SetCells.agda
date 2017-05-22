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

    Sectional : (c : ℂ) (ν : 𝕘 → Set) → Set
    Sectional c ν = (g : 𝔾) → δ c g ≅ (𝕘 st (λ g' → Fiber g g' × ν g'))

    WholeFiber :  Set → (g : 𝔾) (ν : 𝕔 → Set) → Set
    WholeFiber target g ν = (g' : 𝕘) → Fiber g g' → target ≅ Σ 𝕔 (λ c' → ν c' × ∂ c' g')

    Calm : (ν : 𝕔 → Set) → Set
    Calm ν = (g : 𝔾) → WholeFiber ⊤ g ν ⊕ WholeFiber ⊥ g ν

  module PredCalm where
    open FixN
    PredCalm : (n : ℕ) (ν : 𝕧 n → Set) → Set
    PredCalm zero ν = ⊤
    PredCalm (suc n) ν = Calm n ν
  open PredCalm

  module FixN2 (n : ℕ) where
    open FixN n public
    GoodFunc : (c : ℂ) (ν : 𝕘 → Set)  → Set
    GoodFunc c ν = Sectional c ν × PredCalm n ν

    Match : (c : ℂ) → Set₁
    Match c = (𝕔 st (Fiber c) ≅ (𝕘 → Set) st (GoodFunc c))

    PresRel : (c : ℂ) → Match c → Set₁
    PresRel c m =  (c' : 𝕔 st Fiber c) (g' : 𝕘) → Item (proj₁ m c') g' ≡ ∂ (Item c') g'

    AllMatch : Set₁
    AllMatch = (c : ℂ) → Σ (Match c) (PresRel c)

    AllDouble : Set
    AllDouble = (g : 𝔾) → 𝟚 ≅ 𝕘 st (Fiber g)

  open FixN2

  Good∂ : Set
  Good∂ = {n : ℕ} (v₁ : 𝕧 (suc n)) (v₂ : 𝕧 n) → ∂ v₁ v₂ → δ (p v₁) (p v₂)

  GoodOverChain : Set₁
  GoodOverChain = ((n : ℕ) → AllMatch n × AllDouble n) × Good∂

open FixChains

GoodChain : (χ : Chain) → Set₁
GoodChain χ = Σ (OverChain χ) (λ π → GoodOverChain χ π)
