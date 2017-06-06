{-# OPTIONS --without-K --rewriting #-}

module Asdf where

open import HoTT hiding (_≤_)

postulate
  Subset : Set → Set
  Elt : {X : Set} → Subset X → Set
  Real : {X : Set} {s : Subset X} → Elt s → X
  Union : {X Y : Set} (fam1 : Subset X) (fam2 : X → Subset Y) → Subset Y
  _≤_ : {X : Set} → Subset X → Subset X → Set
  UnionSub : {C D : Set} (s : Subset C) (δ : C → Subset D) (σ : Elt s) → δ (Real σ) ≤ Union s δ
  Union≤ : {C D : Set} (s1 s2 : Subset C) (δ : C → Subset D) → Union s1 δ ≤ Union s2 δ
  ≤coe : {C : Set} {s1 s2 : Subset C} → s1 ≤ s2 → Elt s1 → Elt s2

Res : {X Y : Set} → (X → Y) → (s : Subset X) → Elt s → Y
Res f s e = f (Real e)

data feq {X : Set} (𝕀 : Set) : (fam : 𝕀 → X) → Set where
  frefl : (x : X) → feq 𝕀 (λ _ → x)

data Gr : (C : Set) → Set₁ where
  gnil : Gr ⊤
  gcons : (C {D} : Set) (δ : C → Subset D) (G : Gr D)  → Gr C

module Fix {X : Set} where
  Mod : {C : Set} (G : Gr C) → Set
  Cell : {C : Set} (G : Gr C) (M : Mod G) (s : Subset C) → Set
  Compat : {C D : Set} {s : Subset C} (G : Gr D) {M : Mod G} {δ : C → Subset D} {σ : Elt s} → Cell G M (δ (Real σ)) → Cell G M (Union s δ) → Set
  Compat2 : {C : Set} (G : Gr C) {M : Mod G} {s1 s2 : Subset C} → s1 ≤ s2 → Cell G M s1 → Cell G M s2 → Set
  ResC : {C : Set} (G : Gr C) {M : Mod G} {s1 s2 : Subset C} → s1 ≤ s2 → Cell G M s2 → Cell G M s1
  CompatLem : {C D : Set} (G : Gr D) {M : Mod G} {δ : C → Subset D} {s1 s2 : Subset C} (ie : s1 ≤ s2)
     (mc : (c : C) → Cell G M (δ c)) (σ : Elt s1) (cc : Cell G M (Union s2 δ)) →
     Compat G (mc (Real (≤coe ie σ))) cc → Compat G (mc (Real σ)) (ResC G (Union≤ s1 s2 δ) cc)

  Mod (gnil) = ⊤
  Mod (gcons C δ G) = Σ (Mod G) (λ M → (c : C) → Cell G M (δ c))
  Cell (gnil) m s = X
  Cell (gcons C δ G) (M , mc) s = Σ (Cell G M (Union s δ)) (λ oc → (σ : Elt s) → Compat G (mc (Real σ)) oc)
  Compat {s = s} G {δ = δ} {σ} c1 c2 = Compat2 G (UnionSub s δ σ) c1 c2
  Compat2 G ie c1 c2 = ResC G ie c2 == c1
  ResC gnil ie c = c
  ResC (gcons C δ G) {M , mc} {s1 = s1} {s2} ie (cc , compat) = ResC G (Union≤ s1 s2 δ) cc , (λ σ → CompatLem G ie mc σ cc (compat (≤coe ie σ)))
  CompatLem G {M} {δ} {s1} {s2} ie mc σ cc compat = goal where
    goal : ResC G (UnionSub s1 δ σ) (ResC G (Union≤ s1 s2 δ) cc) == (mc (Real σ))
    goal = {!!}

    have : ResC G (UnionSub s2 δ (≤coe ie σ)) cc == mc (Real (≤coe ie σ))
    have = compat
