{-# OPTIONS --without-K --rewriting #-}

module Asdf where

open import HoTT hiding (_∧_ ; Bool ; true ; false ; if_then_else_ )

data Bool : Set where
  true : Bool
  false : Bool

if_then_else_ : ∀ {i} {A : Type i}
  → Bool → A → A → A
if true then t else e = t
if false then t else e = e

data Filt : (n : ℕ) → Set where
  fnil : Filt 0
  fcons : {n : ℕ} → Bool → Filt n → Filt (S n)

data Gr : (n : ℕ) → Set where
  lnil : Gr 0
  lcons : {n : ℕ} → Gr n → Filt n → Gr (S n)

_∧_ : Bool → Bool → Bool
false ∧ _ = false
_ ∧ false = false
true ∧ true = true

_⋆_ : {n : ℕ} → Filt n → Filt n → Filt n
fnil ⋆ fnil = fnil
(fcons b1 f1) ⋆ (fcons b2 f2) = fcons (b1 ∧ b2) (f1 ⋆ f2)

postulate
  ⋆comm : {n : ℕ} (f1 f2 : Filt n) → (f1 ⋆ f2) == (f2 ⋆ f1)

module Fix {X : Set} where
  Mod : {n : ℕ} → Gr n → Set
  Cell : {n : ℕ} → (G : Gr n) (M : Mod G) (f : Filt n) → Set
  CondCompat : (b : Bool) {n : ℕ} (G : Gr n) {M : Mod G} (f1 f2 : Filt n) (c1 : Cell G M f1) (c2 : Cell G M f2) → Set
  Compat : {n : ℕ} (G : Gr n) {M : Mod G} (f1 f2 : Filt n) (c1 : Cell G M f1) (c2 : Cell G M f2) → Set -- f1 might say false when f2 says true





  Mod lnil = ⊤
  Mod (lcons G f) = Σ (Mod G) (λ M → Cell G M f)
  CondCompat b G f1 f2 c1 c2 = if b then Compat G f1 f2 c1 c2 else ⊤
  Cell lnil tt fnil = X
  Cell (lcons G f1) (M , mc) (fcons b f2) = Σ (Cell G M f2) (CondCompat b G f1 f2 mc)
  Compat G fnil fnil c1 c2 = c1 == c2
  Compat (lcons G fG) (fcons true f1) (fcons true f2) c1 c2 = Compat G f1 f2 (fst c1) (fst c2) × {!!}
  Compat (lcons G fG) (fcons true f1) (fcons false f2) c1 c2 = Compat G f1 f2 (fst c1) (fst c2)
  Compat (lcons G fG) (fcons false f1) (fcons true f2) c1 c2 = Compat G f1 f2 (fst c1) (fst c2)
  Compat (lcons G fG) (fcons false f1) (fcons false f2) c1 c2 = Compat G f1 f2 (fst c1) (fst c2)



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
