module InvolutionCells (A : Set) where

open import Data.Nat
open import Data.Unit
open import Data.Bool
open import Data.Product
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import BoolUtil

record InvSet : Set₁ where
  constructor MkInvSet
  field
    # : Set
    ι : # → #
open InvSet

record Bundle : Set₁ where
  constructor MkBundle
  field
    𝔾 : InvSet
    ℂ : InvSet
    ∂ : # ℂ → # 𝔾 → Bool

MinimalFunc : {X : Set} (pred : (X → Bool) → Set) (v : X → Bool) → Set
MinimalFunc {X} pred v = (w : X → Bool) → w ⊑ v → pred w → (x : X) → Bool= (v x) (w x) ≡ true

module FixBundle (β : Bundle) where
  ℂ = Bundle.ℂ β
  𝔾 = Bundle.𝔾 β
  ∂ = Bundle.∂ β
  C = # ℂ
  G = # 𝔾

  ZeroFunc : (C → Bool) → Set
  ZeroFunc v = (g : G) → Calm C (matcher g) (matcher (ι 𝔾 g))
    where
    matcher : G → C → Bool
    matcher = λ g c → (v c) ∧ (∂ c g)

  Functional : (C → Bool) → Set
  Functional v =  (c : C) → v c ≡ true → v (ι ℂ c) ≡ false

  OkayFunc : (C → Bool) → Set
  OkayFunc v = Functional v × ZeroFunc v × NonTriv v

  GoodFunc : (v : C → Bool) → Set
  GoodFunc v = OkayFunc v × MinimalFunc OkayFunc v

  TransferOkay : (it : C → Bool) → OkayFunc it → OkayFunc (λ c → it (ι ℂ c))
  TransferOkay = {!!}

open FixBundle

IncBundle : Bundle → Bundle
IncBundle β@(MkBundle 𝔾 ℂ ∂) =
  MkBundle ℂ (MkInvSet ℂ1 ι1) Item
  where
  ℂ1 : Set
  ℂ1 = ((# ℂ → Bool) st (GoodFunc β))


  ι1 : ℂ1 → ℂ1
  ι1 (it ,, p) = (λ c → it (ι ℂ c)) ,, ({!!} , {!!})

DoubleInv : (B : Set) → InvSet
DoubleInv B = MkInvSet (B × Bool) (λ p → (proj₁ p , not (proj₂ p)))

GiveBundle : ℕ → Bundle
GiveBundle zero = MkBundle (DoubleInv ⊤) (DoubleInv A) (λ a x → Bool= (proj₂ a) (proj₂ x))
GiveBundle (suc n) = IncBundle (GiveBundle n)
