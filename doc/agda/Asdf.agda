{-# OPTIONS --without-K --rewriting #-}

module Asdf where

open import HoTT

data Filt : (n : ℕ) → Set where
  fnil : Filt 0
  fcons : {n : ℕ} → Bool → Filt n → Filt (S n)

data Gr : (n : ℕ) → Set where
  lnil : Gr 0
  lcons : {n : ℕ} → Gr n → Filt n → Gr (S n)

data _■_ : Bool → Bool → Set where
  bool/refl : (b : Bool) → b ■ b
  bool/ie : false ■ true

data _⊑_ : {n : ℕ} → Filt n → Filt n → Set where
  sle/nil : fnil ⊑ fnil
  sle/cons : {n : ℕ} (f1 f2 : Filt n) (b1 b2 : Bool) → b1 ■ b2 → f1 ⊑ f2 → fcons b1 f1 ⊑ fcons b2 f2

module Fix {X : Set} where
  Mod : {n : ℕ} → Gr n → Set
  Cell : {n : ℕ} → (G : Gr n) (M : Mod G) (f : Filt n) → Set
  CondCompat : (b : Bool) {n : ℕ} (G : Gr n) {M : Mod G} (f1 f2 : Filt n) (c1 : Cell G M f1) (c2 : Cell G M f2) → Set
  Compat : {n : ℕ} (G : Gr n) {M : Mod G} (f1 f2 : Filt n) (c1 : Cell G M f1) (c2 : Cell G M f2) → Set -- f1 might say false when f2 says true
  Res : {n : ℕ} (G : Gr n) {M : Mod G} {f1 f2 : Filt n} (ie : f1 ⊑ f2) (c2 : Cell G M f2) → Cell G M f1
  CondCompatLem : {n : ℕ} (G : Gr n) {fstM : Mod G} {f f1 f2 : Filt n} (ie : f1 ⊑ f2) (csndM : Cell G fstM f) (c0 : Cell G fstM f2) {b1 b2 : Bool}
    (b■ : b1 ■ b2)  → CondCompat b2 G f f2 csndM c0 → CondCompat b1 G f f1 csndM (Res G ie c0)
  CompatLem : {n : ℕ} (G : Gr n) {fstM : Mod G} {f f1 f2 : Filt n} (ie : f1 ⊑ f2) (csndM : Cell G fstM f) (c0 : Cell G fstM f2)
      → Compat G f f2 csndM c0 → Compat G f f1 csndM (Res G ie c0)



  Mod lnil = ⊤
  Mod (lcons G f) = Σ (Mod G) (λ M → Cell G M f)
  CondCompat b G f1 f2 c1 c2 = if b then Compat G f1 f2 c1 c2 else ⊤
  Cell lnil tt fnil = X
  Cell (lcons G f1) (M , mc) (fcons b f2) = Σ (Cell G M f2) (CondCompat b G f1 f2 mc)
  Compat G f1 f2 c1 c2 = Σ (f1 ⊑ f2) (λ ie → Res G ie c2 == c1)
  Res lnil sle/nil c = c
  Res (lcons G f) {M} (sle/cons f1 f2 b1 b2 b■ ie) (c0 , compat) = Res G ie c0 , CondCompatLem G ie (snd M) c0 b■  compat
  CondCompatLem G ie c1 c2 (bool/refl true) compat = CompatLem G ie c1 c2 compat
  CondCompatLem G ie c1 c2 (bool/refl false) compat = tt
  CondCompatLem G ie c1 c2 bool/ie compat = tt
  CompatLem lnil sle/nil c1 .c1 (sle/nil , idp) = (sle/nil , idp)
  CompatLem G (sle/cons f1 f2 b1 b2 x ie) c1 c2 (ie2 , reseq) = {!!} , {!!}

open Fix

## : Filt 0
## = fnil

_#_ : {n : ℕ} → Bool → Filt n → Filt (S n)
_#_ = fcons
infixr 20 _#_

_⊞_ : {n : ℕ} → Filt n → Gr n → Gr (S n)
_⊞_ f g = lcons g f
infixr 19 _⊞_



𝕀G0 = ## ⊞ lnil -- one vertex
𝕀G1 = false # ## ⊞ ## ⊞ lnil -- two vertices
𝕀G2 = true # true # ## ⊞ false # ## ⊞ ## ⊞ lnil -- two vertices which are equal

q : {X : Set} (x y : X) (p : x == y) → Mod {X} 𝕀G2
q {X} x y p = final where
  m0 : Σ ⊤ (λ M → X) -- = Mod 𝕀G0
  m0 = tt , x

  m1 : Σ (Mod 𝕀G0) (λ M → Cell 𝕀G0 M (false # ##)) -- = Mod 𝕀G1
  m1 = m0 , (y , tt)

  c1 : Cell 𝕀G0 m0 (true # ##)
  c1 = x , {!!}

  c2 : Cell 𝕀G1 m1 (true # true # ##)
  c2 = c1 , {!!}

  final : Σ (Mod 𝕀G1) (λ M → Cell 𝕀G1 M (true # true # ##))
  final = m1 , c2
