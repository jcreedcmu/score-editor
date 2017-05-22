module ChainInvolutionCells where

open import Data.Nat
open import Data.Unit
open import Data.Bool
open import Data.Product
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; subst; sym)
open import BoolUtil

record InvSet : Set₁ where
  constructor MkInvSet
  field
    # : Set
    ι : # → #
open InvSet

DoubleInv : (B : Set) → InvSet
DoubleInv B = MkInvSet (B × Bool) (λ p → (proj₁ p , not (proj₂ p)))

𝔻 : ((n : ℕ) → InvSet) → (n : ℕ) → InvSet
𝔻 𝕏 zero = DoubleInv ⊤
𝔻 𝕏 (suc n) = 𝕏 n


record Chain : Set₁ where
  constructor MkChain
  field
    𝕏 : (n : ℕ) → InvSet
    δ : (n : ℕ) → # (𝕏 n )→ # (𝔻 𝕏 n) → Bool

module FixChain (χ : Chain) where
  𝕏 = Chain.𝕏 χ
  δ = Chain.δ χ

  module FixN (n : ℕ) where
    ℂ = 𝕏 n
    𝔾 = 𝔻 𝕏 n
    C = # ℂ
    G = # 𝔾
    ∂ = δ n

    matcher : G → (C → Bool) → C → Bool
    matcher = λ g v c → (v c) ∧ (∂ c g)

    ZeroFunc : (C → Bool) → Set
    ZeroFunc v = (g : G) → Calm C (matcher g v) (matcher (ι 𝔾 g) v)

    Functional : (C → Bool) → Set
    Functional v =  (c : C) → v c ≡ true → v (ι ℂ c) ≡ false

    OkayFunc : (C → Bool) → Set
    OkayFunc v = Functional v × ZeroFunc v × NonTriv v

    GoodFunc : (C → Bool) → Set
    GoodFunc v = OkayFunc v × Minimal OkayFunc v

  open FixN public
open FixChain

GoodCell : {n : ℕ} (χ : Chain) (c : # (Chain.𝕏 χ (suc n))) → Set
GoodCell {n} χ@(MkChain 𝕏 δ) c = GoodFunc χ n (δ (suc n) c)

Good : Chain → Set
Good χ@(MkChain 𝕏 δ) = (n : ℕ) (c : # (𝕏 (suc n))) → GoodCell χ c
