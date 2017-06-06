module FuncCellsHott where

open import HoTT hiding (ℤ)

record _st_{a b} (A : Set a) (B : A → Set b) : Set (lmax a b) where
  constructor _,,_
  field
    Item : A
    .Pf : B Item -- proof irrelevance
open _st_ public

𝔻 : ((n : ℕ) → Set) → (n : ℕ) → Set
𝔻 𝕏 0 = ⊥
𝔻 𝕏 1 = ⊤
𝔻 𝕏 (S (S n)) = 𝕏 n

record Chain : Set₁ where
  constructor MkChain
  field
    𝕏 : (n : ℕ) → Set
    δ : (n : ℕ) → 𝔻 𝕏 (S n) → 𝔻 𝕏 n  → Set
  𝕐 : (n : ℕ) → Set
  𝕐 n = 𝔻 𝕏 n

module FixChain (χ : Chain) (Charge : Set) where
  open Chain χ
  F : {n : ℕ} (z : 𝕐 n) → Set
  Fsuc : {n : ℕ} (g : 𝕐 (S n)) → Set -- split this out to satisfy termination checker
  φ : {n : ℕ} {g : 𝕐 (S n)} → F {S n} g → (z : 𝕐 n) → δ n g z → F {n} z

  F {0} ()
  F {S n} g = Fsuc {n} g

  module FixN (n : ℕ) (c : 𝕐 (S (S n))) where
    ℂ = 𝕐 (S (S n))
    𝔾 = 𝕐 (S n)
    ℤ = 𝕐 n
    Section : Set
    Section = (g : 𝔾) → δ (S n) c g → Fsuc {n} g
    record PathsTo (ν : Section) {z : ℤ} (z' : F {n} z) : Set where
      field
        g : 𝔾
        hop1 : δ (S n) c g
        hop2 : δ n g z
        trans : φ (ν g hop1) z hop2 == z'
    Calm : Section → Set
    Calm ν = (z : ℤ) (z1' z2' : F {n} z) → PathsTo ν z1' ≃ PathsTo ν z2' where

  Fsuc {0} tt = Charge
  Fsuc {S n} c = Section st Calm where open FixN n c
  φ {0} g' ()
  φ {S n} = Item
