{-# OPTIONS --without-K --rewriting #-}

module Sandbox where

open import HoTT

data feq {X : Set} (𝕀 : Set) : (fam : 𝕀 → X) → Set where
  frefl : (x : X) → feq 𝕀 (λ _ → x)

data req {X : Set} (𝕀 : Set) : (fam : 𝕀 → X) → Set where
  rrefl : (x : X) (f : 𝕀 → X) (e : (i : 𝕀) → x == f i) → req 𝕀 f


bf : {X : Set} → X → X → Bool → X
bf a b true = a
bf a b false = b

kreq : {X : Set} (x : X) → req Bool (bf x x)
kreq x = rrefl x (bf x x) (λ { true → idp ; false → idp })


data f2eq {X : Set} : (a b c : X)
    (p : req Bool (bf a b))
    (q : req Bool (bf b c))
    (r : req Bool (bf a c)) → Set where
    f2refl : (x : X) → f2eq x x x (kreq x) (kreq x) (kreq x)


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
  Mod eye = EyeMod
