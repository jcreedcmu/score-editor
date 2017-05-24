module FuncCells3 where

open import Data.Nat
open import Data.Unit
open import Data.Product
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.Empty
open import Data.Sum renaming ( _⊎_ to _⊕_ )
open import BoolUtil using (_≅_ ; _st_ ; IsoFor ; MkIsoFor)
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

module FixChain (χ : Chain) (Charge : Set) where
  open Chain χ
  F : {n : ℕ} (z : 𝕐 n) → Set
  Fsuc : {n : ℕ} (g : 𝕐 (suc n)) → Set -- split this out to satisfy termination checker
  φ : {n : ℕ} {g : 𝕐 (suc n)} → F {suc n} g → (z : 𝕐 n) → δ n g z → F {n} z

  F {zero} ()
  F {suc n} g = Fsuc {n} g

  module FixN (n : ℕ) (c : 𝕐 (suc (suc n))) where
    ℂ = 𝕐 (suc (suc n))
    𝔾 = 𝕐 (suc n)
    ℤ = 𝕐 n
    Section : Set
    Section = (g : 𝔾) → δ (suc n) c g → Fsuc {n} g
    record TwoHop (ν : Section) (z : ℤ) (z' : F {n} z) : Set where
      field
        g : 𝔾
        hop1 : δ (suc n) c g
        hop2 : δ n g z
        transport : φ {n} (ν g hop1) z hop2 ≡ z'
    Calm : Section → Set
    Calm ν = (z : ℤ) (z1' z2' : F {n} z) → TwoHop ν z z1' ≅ TwoHop ν z z2'

  Fsuc {zero} tt = Charge
  Fsuc {suc n} c = Section st Calm where open FixN n c
  φ {zero} g' ()
  φ {suc n} = Item
