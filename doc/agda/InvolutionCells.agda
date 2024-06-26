module InvolutionCells (A : Set) where

open import Data.Nat
open import Data.Unit
open import Data.Bool
open import Data.Product
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; subst; sym)
open import BoolUtil

postulate
  funext : {A B : Set} {f g : A → B} → ((x : A) → f x ≡ g x) → f ≡ g

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

module FixBundle (β : Bundle) where
  ℂ = Bundle.ℂ β
  𝔾 = Bundle.𝔾 β
  ∂ = Bundle.∂ β
  C = # ℂ
  G = # 𝔾

  {- XXX should be part of the appropriate records -}
  postulate
    isInv : (ℂ : InvSet) (x : # ℂ) → x ≡ ι ℂ (ι ℂ x)
    pres : (c : C) (g : G) → ∂ (ι ℂ c) g ≡ ∂ c (ι 𝔾 g)

  matcher : G → (C → Bool) → C → Bool
  matcher = λ g v c → (v c) ∧ (∂ c g)

  ZeroFunc : (C → Bool) → Set
  ZeroFunc v = (g : G) → Calm C (matcher g v) (matcher (ι 𝔾 g) v)

  Functional : (C → Bool) → Set
  Functional v =  (c : C) → v c ≡ true → v (ι ℂ c) ≡ false

  OkayFunc : (C → Bool) → Set
  OkayFunc v = Functional v × ZeroFunc v × NonTriv v

  GoodFunc : (v : C → Bool) → Set
  GoodFunc v = OkayFunc v × Minimal OkayFunc v

  EqualMatcher : (it : C → Bool) (g : G)
    → matcher (ι 𝔾 g) it ≡ matcher g (λ c → it (ι ℂ c))
  EqualMatcher it g = funext lemma where
    lemma : (c : C) → (it c) ∧ (∂ c (ι 𝔾 g)) ≡ (it (ι ℂ c)) ∧ (∂ c g)
    lemma c = {!!}
--    lemma : (c : C) → (it c') ∧ (∂ c g) ≡ (it c) ∧ (∂ c' g) ??????

{- This is getting quite hard. Maybe what I actually should do is
require GoodFunc v ∧ GoodFunc (ι v) at the outset; then proving that
the involution of v is still good is merely showing that I have
GoodFunc (ι v) ∧ GoodFunc v, which should be a much easier, merely
shallow swizzling proof. -}

  module FixIt (it : C → Bool) where
    itt = λ c → it (ι ℂ c)

    TransferFunctional : Functional it → Functional itt
    TransferFunctional p = λ c x → p (ι ℂ c) x

    TransferCalm : (g : G)
      → Calm C (matcher (ι 𝔾 g) it) (matcher g it)
      → Calm C (matcher g itt)       (matcher (ι 𝔾 g) itt)
    TransferCalm = {!!}

    TransferZeroFunc : ZeroFunc it → ZeroFunc itt
    TransferZeroFunc p g =
      TransferCalm g psub where
      palt = p (ι 𝔾 g)
      psub = subst (λ ■ → Calm C (matcher (ι 𝔾 g) it) (matcher ■ it)) (sym (isInv 𝔾 g)) palt

    TransferNonTriv : NonTriv it → NonTriv itt
    TransferNonTriv (x , pf) = (ι ℂ x) , subst (λ t → it t ≡ true) (isInv ℂ x) pf

    TransferOkay : OkayFunc it → OkayFunc itt
    TransferOkay (p1 , p2 , p3) =
      TransferFunctional p1 , TransferZeroFunc p2 , TransferNonTriv p3

    TransferMinimal : Minimal OkayFunc it → Minimal OkayFunc itt
    TransferMinimal = {!!}

  open FixIt public

open FixBundle

IncBundle : Bundle → Bundle
IncBundle β@(MkBundle 𝔾 ℂ ∂) =
  MkBundle ℂ (MkInvSet ℂ1 ι1) Item
  where
  ℂ1 : Set
  ℂ1 = ((# ℂ → Bool) st (GoodFunc β))

  ι1 : ℂ1 → ℂ1
  ι1 (it ,, (p1 , p2)) = (λ c → it (ι ℂ c)) ,, (TransferOkay β it p1 , TransferMinimal β it p2)

DoubleInv : (B : Set) → InvSet
DoubleInv B = MkInvSet (B × Bool) (λ p → (proj₁ p , not (proj₂ p)))

GiveBundle : ℕ → Bundle
GiveBundle zero = MkBundle (DoubleInv ⊤) (DoubleInv A) (λ a x → Bool= (proj₂ a) (proj₂ x))
GiveBundle (suc n) = IncBundle (GiveBundle n)
