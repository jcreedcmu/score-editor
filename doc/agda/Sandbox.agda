{-# OPTIONS --without-K --rewriting #-}

module Sandbox where

open import HoTT

data feq {X : Set} (𝕀 : Set) : (fam : 𝕀 → X) → Set where
  frefl : (x : X) → feq 𝕀 (λ _ → x)

data req {X : Set} (𝕀 : Set) : (fam : 𝕀 → X) → Set where
  rrefl : (x : X) (f : 𝕀 → X) (e : (i : 𝕀) → x == f i) → req 𝕀 f

fequp : {X : Set} (𝕀 : Set) (δ : 𝕀 → Set) (fam : 𝕀 → X) (x : X) → Set
fequp 𝕀 δ f x = feq (Σ 𝕀 δ) (f ∘ fst)

data fequ {X : Set} (𝕀 : Set) (δ : 𝕀 → Set) : (fam : 𝕀 → X) → Set where
  furefl : (x : X) (f : 𝕀 → X) → fequp 𝕀 δ f x → fequ 𝕀 δ f

fequk : {X 𝕀 : Set} {δ : 𝕀 → Set} (x : X) → fequ 𝕀 δ (λ _ → x)
fequk x = furefl x (λ _ → x) (frefl x)

bf : {X : Set} → X → X → Bool → X
bf a b true = a
bf a b false = b

data f3eq ({X} 𝕍 𝔼 : Set) (∂ : 𝔼 → 𝕍 → Set) : (vm : 𝕍 → X)
  (em : (e : 𝔼) → fequ 𝕍 (∂ e) vm) → Set where
  f3refl : (x : X) → f3eq 𝕍 𝔼 ∂ (λ _ → x) (λ _ → fequk x)

f3equp : ({X} 𝕍 𝔼 : Set) (δev : 𝔼 → 𝕍 → Set) (δe : 𝔼 → Set) (δv : 𝕍 → Set)
    (vm : 𝕍 → X) (em : (e : 𝔼) → fequ 𝕍 (δev e) vm) → Set
f3equp {X} 𝕍 𝔼 δev δe δv vm em =
  f3eq {X} (Σ 𝕍 δv) (Σ 𝔼 δe) (λ e v → δev (fst e) (fst v)) (vm ∘ fst) {!!}


data 𝕍 : Set where
  𝕍a 𝕍b 𝕍c 𝕍d : 𝕍

data 𝔼 : Set where
  𝔼f 𝔼g 𝔼h 𝔼k 𝔼m : 𝔼

data 𝔽 : Set where
  𝔽α 𝔽β : 𝔽

postulate
  ∂ev : 𝔼 → 𝕍 → Set
  ∂fe : 𝔽 → 𝔼 → Set
  ∂fv : 𝔽 → 𝕍 → Set

module FixX (X : Set) where
  record Bundle1 : Set₁ where
    field
      VC : Set
      EC : Set
      δ : EC → VC → Set

  record Bundle1Mod (f : Bundle1) : Set where
    open Bundle1 f
    field
      Vm : VC → X
      Em : (e : EC) → feq (Σ VC (δ e)) (λ b → Vm (fst b))

{-
  record EyeMod : Set where
    field
      VA VB VC VD : X
      Ef : req Bool (bf VA VB)
      Eg : req Bool (bf VB VC)
      Eh : req Bool (bf VB VD)
      Ek : req Bool (bf VA VD)
      Em : req Bool (bf VD VC)
      Fα : f2eq VA VB VD Ef Eh Ek
      Fβ : f2eq VB VD VC Eh Em Eg
-}


  record EyeMod2 : Set where
    field
      2V : 𝕍 → X
      2E : (e : 𝔼) → fequ 𝕍 (∂ev e) 2V

  Foo : Set
  Foo =
    (2V : 𝕍 → X)
    (2E : (e : 𝔼) → fequ 𝕍 (∂ev e) 2V)
    (f : 𝔽) → f3eq {X} (Σ 𝕍 (∂fv f)) (Σ 𝔼 (∂fe f)) (λ e v → ∂ev (fst e) (fst v)) (2V ∘ fst)
      (λ e → {!!})

  data Gr : Set₁ where
    gnil : Gr
    gsingle : Gr
    gdouble : Gr
    gvert : Set → Gr
    gedge : Gr
    g3edge : Gr
    b1g : Bundle1 → Gr
    eye : Gr

  data 3eq : X → X → X → Set where
    3refl : (x : X) → 3eq x x x

  Mod : (G : Gr) → Set

  Mod gnil = ⊤
  Mod gsingle = X
  Mod gdouble = X × X
  Mod (gvert C) = C → X
  Mod gedge = Σ X (λ x → Σ X (λ y → x == y))
  Mod g3edge = Σ X (λ x → Σ X (λ y → Σ X (λ z → 3eq x y z)))
  Mod (b1g b1) = Bundle1Mod b1
  Mod eye = EyeMod2

{-
kreq : {X : Set} (x : X) → req Bool (bf x x)
kreq x = rrefl x (bf x x) (λ { true → idp ; false → idp })


data f2eq {X : Set} : (a b c : X)
    (p : req Bool (bf a b))
    (q : req Bool (bf b c))
    (r : req Bool (bf a c)) → Set where
    f2refl : (x : X) → f2eq x x x (kreq x) (kreq x) (kreq x)


∂ev : 𝔼 → 𝕍 → Set
∂ev 𝔼f 𝕍a = ⊤
∂ev 𝔼f 𝕍b = ⊤
∂ev 𝔼k 𝕍a = ⊤
∂ev 𝔼k 𝕍d = ⊤
∂ev 𝔼h 𝕍b = ⊤
∂ev 𝔼h 𝕍d = ⊤
∂ev 𝔼g 𝕍b = ⊤
∂ev 𝔼g 𝕍c = ⊤
∂ev 𝔼m 𝕍d = ⊤
∂ev 𝔼m 𝕍c = ⊤
∂ev _ _ = ⊥

∂fe : 𝔽 → 𝔼 → Set
∂fe 𝔽α 𝔼f = ⊤
∂fe 𝔽α 𝔼h = ⊤
∂fe 𝔽α 𝔼k = ⊤
∂fe 𝔽β 𝔼g = ⊤
∂fe 𝔽β 𝔼h = ⊤
∂fe 𝔽β 𝔼m = ⊤
∂fe _ _ = ⊥

∂fv : 𝔽 → 𝕍 → Set
∂fv 𝔽α 𝕍a = ⊤
∂fv 𝔽α 𝕍b = ⊤
∂fv 𝔽α 𝕍d = ⊤
∂fv 𝔽β 𝕍b = ⊤
∂fv 𝔽β 𝕍d = ⊤
∂fv 𝔽β 𝕍c = ⊤
∂fv _ _ = ⊥
-}
