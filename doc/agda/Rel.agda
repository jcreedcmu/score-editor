{-# OPTIONS --without-K --rewriting #-}

module Rel where

open import HoTT

{-
record Foo1 : Set₁ where
  field
    ∂ : ℕ → Set
    C : ℕ → Set
    δ : (n : ℕ) → C n → ∂ n
    □ : {m n : ℕ} (t : m < n) (b : ∂ n) → Set
    φ : {m n : ℕ} (t : m < n) (b : ∂ n) → □ t b → C m
    □t : {ℓ m n : ℕ} {t0 : ℓ < m} {t1 : m < n} {b : ∂ n} (s1 : □ t1 b) (s2 : □ t0 (δ m (φ t1 b s1))) → □ (<-trans t0 t1) b
    φt : (ℓ m n : ℕ) (t0 : ℓ < m) (t1 : m < n) (b : ∂ n) (s1 : □ t1 b) (s2 : □ t0 (δ m (φ t1 b s1))) → φ (<-trans t0 t1) b (□t s1 s2) == φ t0 (δ m (φ t1 b s1)) s2
-}

record Gr : Set₁ where
  field
    C : Set -- cells
    □ : C → Set -- "holes" in a cell, places for subcells
    φ : {c : C} → □ c → C -- what subcell actually fills the hole?
    t : {c : C} (s1 : □ c) (s2 : □ (φ s1)) → Σ (□ c) (λ s → φ s == φ s2)
    -- the property that every subhole of a subcell is also a subcell, and its filler
    -- doesn't depend on whether you regard it as a direct or indirect subcell

data 𝟚 : Set where
  𝟘 𝟙 : 𝟚

data H : Set where
  vA vB eL eR : H

module _ (G : Gr) where
  open Gr G
  record Mor (A B : C) : Set where
    field
      R : C
      holes : 𝟚 ≃ □ R
      hole1 : φ (–> holes 𝟘) == A
      hole2 : φ (–> holes 𝟙) == B

module _ {G : Gr} {A B : Gr.C G} {f : Mor G A B} where
  open Gr G
  open Mor f
  record Functional : Set where
    field
      ε η : C
      holesε : H ≃ □ ε
      holesη : H ≃ □ η
      holeεA : φ (–> holesε vA) == A
      holeεB : φ (–> holesε vB) == B
      holeεL : φ (–> holesε eL) == R
      holeεR : φ (–> holesε eR) == R
      εLA :  <– holesε (fst (t (–> holesε eL) (coe! (ap □ holeεL) (–> holes 𝟘)))) == vA
      εLB :  <– holesε (fst (t (–> holesε eL) (coe! (ap □ holeεL) (–> holes 𝟙)))) == vB
      εRA :  <– holesε (fst (t (–> holesε eR) (coe! (ap □ holeεR) (–> holes 𝟘)))) == vA
      εRB :  <– holesε (fst (t (–> holesε eR) (coe! (ap □ holeεR) (–> holes 𝟙)))) == vB
