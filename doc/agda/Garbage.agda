{-

module Fix where
  record ChangeStruct : Set₁ where
    field
      Δ : {V : Set} → V → Set
      _⊕_ : {V : Set} → (v : V) (dv : Δ v) → V
      𝟘 : {V : Set} (v : V) → Δ v

module FixCh (ξ : Fix.ChangeStruct) where
  open Fix
  open ChangeStruct ξ
  Deriv : {A B : Set} (f : A → B) (f' : (a : A) → Δ a → Δ (f a)) → Set
  Deriv {A} f f' = (a : A) (da : Δ a) → f (a ⊕ da) == ((f a) ⊕ (f' a da))

  fΔ : {A B : Set} → (A → B) → Set
  fΔ {A} f = Σ ((a : A) (da : Δ a) → Δ (f a)) (λ df → (a : A) (da : Δ a) → (f a ⊕ df a da) == (f (a ⊕ da) ⊕ df (a ⊕ da) (𝟘 (a ⊕ da))))
  _f⊕_ : {A B : Set} → (f : A → B) (df : fΔ f) → (A → B)
  (f f⊕ (df1 , df2)) v = f v ⊕ df1 v (𝟘 v)
--  f𝟘 : {A B : Set} (f : A → B) → fΔ f
--  f𝟘 f = {!!} , {!!}

module Fix2 where


  record ChangeStruct : Set₁ where
    field
      E : {V : Set} → V → V → Set
      Δ : {V : Set} → V → Set
      cod : {V : Set} {v : V} (dv : Δ v) → V
      𝟘 : {V : Set} (v : V) → Δ v

module FixCh2 (ξ : Fix2.ChangeStruct) where
  open Fix2
  open ChangeStruct ξ
  Deriv : {A B : Set} (f : A → B) (f' : (a : A) → Δ a → Δ (f a)) → Set
  Deriv {A} f f' = (a : A) (da : Δ a) → f (cod da) == (cod (f' a da))

  -- Deriv2 : {A B : Set} (f : A → B) (f' : (a b : A) → E a b → E (f a) (f b)) → Set
  -- Deriv2 {A} f f' = ⊤

  -- fΔ2 : {A B : Set} → (A → B) → Set
  -- fΔ2 {A} f = Σ ((a : A) (da : Δ a X1) → Δ (f a) (X2 a)) (λ df → (a : A) (da : Δ a (X1 a)) → X2 a == cod (df (cod da) (𝟘 (X3 a))))

  fΔ : {A B : Set} → (A → B) → Set
  fΔ {A} f = Σ ((a : A) (da : Δ a) → Δ (f a)) (λ df → (a : A) (da : Δ a) → cod (df a da) == cod (df (cod da) (𝟘 (cod da))))
  fcod : {A B : Set} {f : A → B} (df : fΔ f) → (A → B)
  fcod (df1 , df2) v = cod (df1 v (𝟘 v))

  fpar : {A B : Set} {f : A → B} (df : fΔ f) (a : A) → Δ (fst df a (𝟘 a))
  fpar = {!!}
-}

--  f𝟘 : {A B : Set} (f : A → B) → fΔ f
--  f𝟘 f = {!!} , {!!}


{-
ξ : Set → Set₁
ξ V = Σ (V → Set) (λ Δ → (v : V) (dv : Δ v) → V)

Gr : (V : Set) → Set₁
Gr V = V → V → Set

thm : (V : Set) → ξ V ≃ Gr V
thm V = equiv into out zig zag where
  into : ξ V → Gr V
  into (Δ , _⊕_) v1 v2 = Σ (Δ v1) (λ dv → (v1 ⊕ dv) == v2)
  out : Gr V → ξ V
  out G = (λ v1 → Σ V (G v1)) , (λ _ pr → fst pr)
  zig : (G : Gr V) → into (out G) == G
  zig G = λ= (λ v1 → λ= (λ v2 → lem v1 v2)) where
    lem : (v1 v2 : V) → Σ (Σ V (λ v2 → G v1 v2)) (λ dv → fst dv == v2) == G v1 v2
    lem = {!!}
  zag : (a : ξ V) → out (into a) == a
  zag (Δ , _⊕_) = pair= (λ= lem1) {!!} where
    lem1 : (v1 : V) → Σ V (λ v2 → Σ (Δ v1) (λ dv → (v1 ⊕ dv) == v2)) == Δ v1
    lem1 = {!!}
-}

{-
open import Agda.Builtin.List
open import Agda.Builtin.Unit public using (⊤; tt)
open import Agda.Builtin.Nat

open import Agda.Builtin.Reflection as Builtin

data ℕ : Set where
  O : ℕ
  S : ℕ → ℕ

record Foo : Set where
  inductive
  field
    foo : ℕ
    bar : ℕ
open Foo

swap : Foo → Foo
swap record { foo = O ; bar = bar₁ } = record { foo = bar₁ ; bar = S O }
swap record { foo = S _ ; bar = bar₁ } = record { foo = bar₁ ; bar = O }


z : Name
z = quote swap

unArg : ∀ {A} → Arg A → A
unArg (arg _ x) = x

macro
    plus-to-times : Term → Term → TC ⊤
    plus-to-times (def (quote _+_) (a ∷ b ∷ [])) hole = unify hole (unArg a)
    plus-to-times v hole = unify hole v

data _≡_ {A : Set} : A → A → Set where
  refl : {a : A} → a ≡ a

thm : (a b c : Nat) → (plus-to-times (c * (a * b))) ≡ (c * (a * b))
thm a b c = refl

y : TC ℕ
y = bindTC (quoteTC swap) (λ swp → unquoteTC {A = ℕ} swp)
-}

{-

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


-}

{-
module Asdf where

open import HoTT hiding (_≤_)


data feq {X : Set} (𝕀 : Set) : (fam : 𝕀 → X) → Set where
  frefl : (x : X) → feq 𝕀 (λ _ → x)

data Opt (X : Set) : Set where
  None : Opt X
  Some : X → Opt X

module Fix {X : Set} where
  data Mod : Set
  ModPt : Mod → Set
  Compat : {M : Mod} → ModPt M → Set

  Cell : Mod → Set
  Cell M = (m : ModPt M) → Opt (Compat m)

  Good : {M : Mod} (m : ModPt M) (co : Opt(Compat m)) → Set
  IdCompat : {M : Mod} (m : ModPt M) → Compat m
  IdGood : {M : Mod} (m : ModPt M) (c : Cell M) → Good m (c m)

  data Mod where
    mnil : X → Mod
    mcons : (M : Mod) (c : Cell M) → Mod

  ModPt (mnil x) = ⊥
  ModPt (mcons M c) = Opt (ModPt M)

  Compat {mnil x} ()
  Compat {mcons M c} None = (m : ModPt M) → Good m (c m)
  Compat {mcons M c} (Some m) = Compat {M} m

  Good m None = ⊤
  Good m (Some cmp) = cmp == IdCompat m

  IdCompat {mnil x} ()
  IdCompat {mcons M c} None m = IdGood m c
  IdCompat {mcons M c} (Some m) = IdCompat m

  IdGood {M} m c = yield (c m) where
    yield : (opt : Opt (Compat m)) → Good m opt
    yield None = tt
    yield (Some cmp) = {!!}
-}


{---- ??? ----}
