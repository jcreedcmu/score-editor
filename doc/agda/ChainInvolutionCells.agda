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
    isInv : (x : #) → ι (ι x) ≡ x
open InvSet

DoubleInv : (B : Set) → InvSet
DoubleInv B = MkInvSet (B × Bool) (λ p → (proj₁ p , not (proj₂ p))) isInvPf where
  isInvPf : (p : B × Bool) → (proj₁ p , not (not (proj₂ p))) ≡ p
  isInvPf (b , false) = refl
  isInvPf (b , true) = refl

𝔻 : ((n : ℕ) → InvSet) → (n : ℕ) → InvSet
𝔻 𝕏 zero = DoubleInv ⊤
𝔻 𝕏 (suc n) = 𝕏 n

record Chain : Set₁ where
  constructor MkChain
  field
    𝕏 : (n : ℕ) → InvSet
    δ : (n : ℕ) → # (𝕏 n) → # (𝔻 𝕏 n) → Bool

module FixChain (χ : Chain) where
  𝕏 = Chain.𝕏 χ
  δ = Chain.δ χ

  module FixN (n : ℕ) where
    ℍ = 𝕏 (suc n)
    ℂ = 𝕏 n
    𝔾 = 𝔻 𝕏 n
    H = # ℍ
    C = # ℂ
    G = # 𝔾
    ∂ = δ n
    ∂' = δ (suc n)

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

    Goodδ : Set
    Goodδ = (c : C) (g : G) → ∂ (ι ℂ c) (ι 𝔾 g) ≡ ∂ c g

    GoodCells : Set
    GoodCells = (h : H) → GoodFunc (δ (suc n) h)

    GoodAtN : Set
    GoodAtN = Goodδ × GoodCells

  open FixN public

  GoodChain : Set
  GoodChain = (n : ℕ) → GoodAtN n

open FixChain
