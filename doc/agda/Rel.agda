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

record RelG : Set₁ where
  field
    C : Set
    □ : C → Set
    φ : {c : C} → □ c → C
    t : {c : C} (s1 : □ c) (s2 : □ (φ s1)) → Σ (□ c) (λ s → φ s == φ s2)
