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
    H : C → C → Set n
    comp : {c d e : C} → H c d → H d e → H c e
    assoc : {b c d e : C} (f : H b c) (g : H c d) (h : H d e) → comp (comp f g) h == comp f (comp g h)

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
SG = MkGr SGDat H comp assoc where
   C = SGDat
   H : C → C → Set₁
   H (SGSet x) d = ⊥
   H (SGRel I f R) z = Σ I (λ i → SGSet (f i) == z)
   H (SG2Rel I f J k R) z = Σ I (λ i → SGSet (f i) == z) ⊔ Σ J thingy where
     thingy : J → Set₁
     thingy j = SGRel I0 (f ∘ η) R0 == z where open RelOver (k j)
   comp : {c d e : C} → H c d → H d e → H c e
   comp {SGSet x} {d} {e} () g
   comp {SGRel I f R} {.(SGSet (f fst₁))} {e} (fst₁ , idp) ()
   comp {SG2Rel I f J₁ k R} {.(SGSet (f fst₁))} {e} (inl (fst₁ , idp)) ()
   comp {SG2Rel I f J₁ k R} {.(SGRel (RelOver.I0 (k j)) (λ x → f (RelOver.η (k j) x)) (RelOver.R0 (k j)))} {.(SGSet (f (RelOver.η (k j) i0)))} (inr (j , idp)) (i0 , idp) =
     inl (RelOver.η (k j) i0 , idp)
   assoc : {b c d e : C} (f : H b c) (g : H c d) (h : H d e) → comp (comp f g) h == comp f (comp g h)
   assoc {SGSet x} {c} {d} {e} () g h
   assoc {SGRel I f R} {.(SGSet (f fst₁))} {d} {e} (fst₁ , idp) () h
   assoc {SG2Rel I f J₁ k R} {.(SGSet (f fst₁))} {d} {e} (inl (fst₁ , idp)) () h
   assoc {SG2Rel I f J₁ k R} {.(SGRel (RelOver.I0 (k fst₁)) (λ x → f (RelOver.η (k fst₁) x)) (RelOver.R0 (k fst₁)))} {.(SGSet (f (RelOver.η (k fst₁) fst₂)))} {e} (inr (fst₁ , idp)) (fst₂ , idp) ()
