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
  Res : {n : ℕ} (G : Gr n) {M : Mod G} ({f1} f2 : Filt n) (c2 : Cell G M f1) → Cell G M (f1 ⋆ f2)
--  CondCompatLem : {n : ℕ} (G : Gr n) {fstM : Mod G} {f f1 f2 : Filt n} (ie : f1 ⊑ f2) (csndM : Cell G fstM f) (c0 : Cell G fstM f2) {b1 b2 : Bool}
--    (b■ : b1 ■ b2)  → CondCompat b2 G f f2 csndM c0 → CondCompat b1 G f f1 csndM (Res G ie c0)
  CompatLem : {n : ℕ} (G : Gr n) {M : Mod G} {f f1 f2 : Filt n} (mc : Cell G M f) (c0 : Cell G M f1)
      → Compat G f f1 mc c0  → Compat G f (f1 ⋆ f2) mc (Res G f2 c0)



  Mod lnil = ⊤
  Mod (lcons G f) = Σ (Mod G) (λ M → Cell G M f)
  CondCompat b G f1 f2 c1 c2 = if b then Compat G f1 f2 c1 c2 else ⊤
  Cell lnil tt fnil = X
  Cell (lcons G f1) (M , mc) (fcons b f2) = Σ (Cell G M f2) (CondCompat b G f1 f2 mc)
  Compat G {M} f1 f2 c1 c2 = Res G f1 c2 == coe (ap (Cell G M) (⋆comm f1 f2)) (Res G f2 c1)
  Res G {M} {fnil} fnil x = x
  Res (lcons G fG) {M , mc} {fcons true f1} (fcons true f2) (c0 , compat) = Res G f2 c0 , CompatLem G mc c0 compat
  Res (lcons G fG) {M , mc} {fcons true f1} (fcons false f2) (c0 , compat) = Res G f2 c0 , tt
  Res (lcons G fG) {M , mc} {fcons false f1} (fcons b2 f2) (c0 , compat) = Res G f2 c0 , tt
  CompatLem lnil {unit} {fnil} {fnil} {fnil} mc c0 compat = compat
  CompatLem (lcons G x) {M , mc} {fcons b f} {fcons true f1} {fcons true f2} (mcc , mccompat) (c0c , c0compat) compat = {!!}
  CompatLem (lcons G x) {M , mc} {fcons b f} {fcons false f1} {fcons b2 f2} (mcc , mccompat) (c0c , c0compat) compat = {!!}
  CompatLem (lcons G x) {M , mc} {fcons b f} {fcons true f1} {fcons false f2} (mcc , mccompat) (c0c , c0compat) compat = {!!}



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
