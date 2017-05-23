module FuncCells2Examples where

open import Data.Nat
open import Data.Unit
open import Data.Bool
open import Data.Product
open import Relation.Binary.PropositionalEquality using (_≡_ ; subst ; sym ; cong-app ; refl)
open import Data.Empty
open import BoolUtil using (_≅_ ; _st_ ; 𝟚 ; IsoFor ; MkIsoFor ; cong-iapp )
open import FuncCells2

0Chain : Chain
0Chain = MkChain 𝕏 δ where
  𝕏 : (n : ℕ) → Set
  𝕏 n = ⊥
  δ : (n : ℕ) → 𝔻 𝕏 (suc n) → 𝔻 𝕏 n  → Set
  δ zero g ()
  δ (suc n) () z

0OverChain : OverChain 0Chain
0OverChain = MkOverChain (λ {n} {c} → φ {n} {c}) (λ {n} → θ {n}) where
  open Chain 0Chain
  φ : {n : ℕ} {g : 𝕐 (suc n)} → 𝟚 → (z : 𝕐 n) → .(δ n g z) → 𝟚
  φ {zero} {g} t () d
  φ {suc n} {()} t z d
  θ : {n : ℕ} → 𝕏 n → 𝕐 n → Set
  θ {n} () g

0GoodChain : GoodChain 0Chain
0GoodChain = 0OverChain , match where
  open Fix 0Chain 0OverChain
  match : (n : ℕ) → MatchAt n
  match n ()

VChain : (A : Set) → Chain
VChain A = MkChain 𝕏 δ where
  𝕏 : (n : ℕ) → Set
  𝕏 0 = A
  𝕏 (suc n) = ⊥
  δ : (n : ℕ) → 𝔻 𝕏 (suc n) → 𝔻 𝕏 n  → Set
  δ 0 c ()
  δ 1 c tt = ⊤
  δ (suc (suc n)) () g


VOverChain : (A : Set) → OverChain (VChain A)
VOverChain A = MkOverChain (λ {n} {c} → φ {n} {c}) (λ {n} → θ {n})
  where
  open Chain (VChain A)
  φ : {n : ℕ} {g : 𝕐 (suc n)} → 𝟚 → (z : 𝕐 n) → .(δ n g z) → 𝟚
  φ {0} {g} t () d
  φ {1} {c} t tt d = t
  φ {suc (suc n)} {()} t g d
  θ : {n : ℕ} → 𝕏 n → 𝕐 n → Set
  θ {0} g ()
  θ {suc n} () z

VGoodChain : (A : Set) → GoodChain (VChain A)
VGoodChain A = VOverChain A , match where
  open Fix (VChain A) (VOverChain A)
  open Chain (VChain A)
  open OverChain (VOverChain A)
  TrivCalm : (a : A) (t : 𝟚) → Calm 0 a (φ {1} {a} t)
  TrivCalm a t ()

  φmono : (c : A) (t u : 𝟚) → (λ g d → t) ≡ (λ g d → u) → t ≡ u
  φmono c t u pf = cong-app (cong-app pf tt) tt

  φepi : (c : A) (b : (z : 𝕐 1) → (δ 1 c z) → 𝟚) → Σ 𝟚 (λ a → φ {1} {c} a ≡ b)
  φepi c b = b tt tt , refl

  match : (n : ℕ) → MatchAt n
  match zero c = MkIsoFor (TrivCalm c) (φmono c) (λ b _ → φepi c b)
  match (suc n) ()
