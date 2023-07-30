module DirCells where

open import Level using (_⊔_)
open import Data.Nat hiding (_⊔_)
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

record FibChain : Set₁ where
  constructor MkChain
  field
    𝕏 : (n : ℕ) → Set
    δ : (n : ℕ) → 𝔻 𝕏 (suc n) → 𝔻 𝕏 n  → Set
    F : {n : ℕ} (z : 𝔻 𝕏 n) → Set
    φ : {n : ℕ} {g : 𝔻 𝕏 (suc n)} → F {suc n} g → (z : 𝔻 𝕏 n) → δ n g z → F {n} z
    $t $f : {n : ℕ} (z : 𝔻 𝕏 n) → F {n} z
  𝕐 : (n : ℕ) → Set
  𝕐 n = 𝔻 𝕏 n

record uΣ {a b} (A : Set a) (B : A → Set b) : Set (a ⊔ b) where
  field
    uitem : A
    upf : B uitem
    uupf : (x : A) → B x → x ≡ uitem

module FixFibChain (χ : FibChain) (Charge : Set) where
  open FibChain χ

  csub : (n : ℕ) → Set₁
  csub n = 𝕐 n → Set

  module FixN (n : ℕ) where
    ℂ = 𝕐 (suc (suc n))
    𝔾 = 𝕐 (suc n)
    𝔾sub = csub (suc n)
    ℤ = 𝕐 n
    ℤsub = csub n

    inBdOf : (tgt : (z : ℤ) → F {n} z) → (g : 𝔾) (z : ℤ) → Set
    inBdOf tgt g z = Σ (δ n g z) (λ m → φ ($t g) z m ≡ tgt z)

    inDomOf : (g : 𝔾) (z : ℤ) → Set
    inDomOf = inBdOf $f

    inCodOf : (g : 𝔾) (z : ℤ) → Set
    inCodOf = inBdOf $t

    record Ancestor (g* : 𝔾sub) (z : ℤ) : Set where
      field
        g : 𝔾
        g∈g* : g* g
        m : δ n g z
    inBdOf* : (tgt : (z : ℤ) → F {n} z) (g* : 𝔾sub) (z : ℤ) → Set
    inBdOf* tgt g* z = uΣ (Ancestor g* z) (λ a → φ ($t (g a)) z (m a) ≡ tgt z)
      where open Ancestor

    inDomOf* : (g* : 𝔾sub) (z : ℤ) → Set
    inDomOf* = inBdOf* $f

    inCodOf* : (g* : 𝔾sub) (z : ℤ) → Set
    inCodOf* = inBdOf* $t
  open FixN

  Models : (n : ℕ) (X : Set) → Set

  ModelTp : (n : ℕ) (X : Set) (m : Models n X) (c : 𝕏 n) → Set
  ModelTp zero X m = λ c → X
  ModelTp (suc zero) X m = {!proj₂ m!}
  ModelTp (suc (suc n)) X m = {!!}


  -- Models is (-1)-indexed: Models 1 X says that every 0-cell has an image in X
  Models zero X = ⊤
  Models (suc n) X = Σ (Models n X) (λ prev → (x : 𝕏 n) → ModelTp n X prev x)
