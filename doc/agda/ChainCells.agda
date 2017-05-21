module ChainCells (A : Set) where

open import Data.Nat
open import Data.Unit
open import Data.Bool
open import Data.Product
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Util

record Bundle : Set₁ where
  constructor MkBundle
  field
    𝔾 : Set
    ℂ : Set
    ∂ : ℂ → 𝔾 → Tern

ZeroFunc : (β : Bundle) → (Bundle.ℂ β → Tern) → Set
ZeroFunc (MkBundle 𝔾 ℂ ∂) v = (g : 𝔾) → calm (λ e → v e ** ∂ e g)

OkayFunc : (β : Bundle) (v : Bundle.ℂ β → Tern) → Set
OkayFunc β v = ZeroFunc β v × NonTriv v

MinimalFunc : {X : Set} (pred : (X → Tern) → Set) (v : X → Tern) → Set
MinimalFunc {X} pred v = (w : X → Tern) → w ⊑ v → pred w → (x : X) → Tern= (v x) (w x) ≡ true

GoodFunc : (β : Bundle) (v : Bundle.ℂ β → Tern) → Set
GoodFunc β v = OkayFunc β v × MinimalFunc (OkayFunc β) v

IncBundle : Bundle → Bundle
IncBundle β@(MkBundle 𝔾 ℂ ∂) = MkBundle ℂ ((ℂ → Tern) st (GoodFunc β)) Item

GiveBundle : ℕ → Bundle
GiveBundle zero = MkBundle ⊤ A (λ a _ → t+)
GiveBundle (suc n) = IncBundle (GiveBundle n)
