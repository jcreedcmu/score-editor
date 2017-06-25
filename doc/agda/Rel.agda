{-# OPTIONS --without-K --rewriting #-}

module Rel where

open import HoTT hiding (⊥)

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

record Gr {n} : Set (lsucc n) where
  constructor MkGr
  field
    C : Set n -- cells
    □ : C → Set -- "holes" in a cell, places for subcells
    φ : (c : C) → □ c → C -- what subcell actually fills the hole?
    t : {c : C} (s1 : □ c) (s2 : □ (φ c s1)) → Σ (□ c) (λ s → φ c s == φ (φ c s1) s2)
    -- the property that every subhole of a subcell is also a subcell, and its filler
    -- doesn't depend on whether you regard it as a direct or indirect subcell

record RelOver (I : Set) (f : I → Set) : Set₁ where
  field
    I0 : Set
    η : I0 → I
    R0 : Π I0 (f ∘ η) → Set

inh : {I : Set} {f : I → Set} → RelOver I f → Π I f → Set
inh r vv = R0 (λ i0 → vv (η i0)) where open RelOver r

data SGDat : Set₁ where
  SGSet : Set → SGDat
  SGRel : (I : Set) (f : I → Set) (R : Π I f → Set) → SGDat
  SG2Rel : (I : Set) (f : I → Set) (J : Set) (k : J → RelOver I f) (R : (vv : Π I f) → ((j : J) → inh (k j) vv) → Set) → SGDat

data ⊥ {n} : Set n where

SG : Gr
SG = MkGr SGDat □ φ t where
   C = SGDat
   □ : C → Set
   □ (SGSet _) = ⊥
   □ (SGRel I f R) = I
   □ (SG2Rel I f J k R) = I ⊔ J
   φ : (c : C) → □ c → C
   φ (SGSet _) ()
   φ (SGRel I f R) i = SGSet (f i)
   φ (SG2Rel I f J k R) (inl i) = SGSet (f i)
   φ (SG2Rel I f J k R) (inr j) = SGRel I0 (f ∘ η) R0 where open RelOver (k j)
   t : {c : C} (s1 : □ c) (s2 : □ (φ c s1)) → Σ (□ c) (λ s → φ c s == φ (φ c s1) s2)
   t {SGSet _} ()
   t {SGRel I f R} s1 ()
   t {SG2Rel I f J k R} (inl i) ()
   t {SG2Rel I f J k R} (inr j) i0 = (inl (η i0)) , idp where open RelOver (k j)
