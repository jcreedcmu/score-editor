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

𝕔 = λ β → # (Bundle.ℂ β)

ZeroFunc : (β : Bundle) → (𝕔 β → Bool) → Set
ZeroFunc (MkBundle 𝔾 ℂ ∂) v = (g : # 𝔾) → Calm (# ℂ) (matcher g) (matcher (ι 𝔾 g))
  where
  matcher : # 𝔾 → # ℂ → Bool
  matcher = λ g c → (v c) ∧ (∂ c g)

Functional : (S : InvSet) → (# S → Bool) → Set
Functional S v =  (s : # S) → v s ≡ true → v (ι S s) ≡ false

OkayFunc : (β : Bundle) → (𝕔 β → Bool) → Set
OkayFunc β@(MkBundle 𝔾 ℂ ∂) v = Functional ℂ v × ZeroFunc β v × NonTriv v

MinimalFunc : {X : Set} (pred : (X → Bool) → Set) (v : X → Bool) → Set
MinimalFunc {X} pred v = (w : X → Bool) → w ⊑ v → pred w → (x : X) → Bool= (v x) (w x) ≡ true

GoodFunc : (β : Bundle) (v : 𝕔 β → Bool) → Set
GoodFunc β v = OkayFunc β v × MinimalFunc (OkayFunc β) v

IncBundle : Bundle → Bundle
IncBundle β@(MkBundle 𝔾 ℂ ∂) =
  MkBundle ℂ (MkInvSet ((# ℂ → Bool) st (GoodFunc β)) (λ x → x)) Item

DoubleInv : (B : Set) → InvSet
DoubleInv B = MkInvSet (B × Bool) (λ p → (proj₁ p , not (proj₂ p)))

GiveBundle : ℕ → Bundle
GiveBundle zero = MkBundle (DoubleInv ⊤) (DoubleInv A) (λ a x → Bool= (proj₂ a) (proj₂ x))
GiveBundle (suc n) = IncBundle (GiveBundle n)
