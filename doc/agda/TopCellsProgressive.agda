{-# OPTIONS --without-K --rewriting #-}

module TopCellsProgressive where

open import HoTT

data Gr : (C : Set) → Set₁ where
  gnil : Gr ⊤
  gcons : (C {D} : Set) (δ : (C → D → Set)) → Gr D → Gr C

module FixX (X : Set) where

  data RawMod : {C : Set} (G : Gr C) → Set₁
  data RawMod where
    rnil : RawMod gnil
    rcons : {C D : Set} {G : Gr D} {δ : (C → D → Set)}
      (R : RawMod G) (xofc : C → X) → RawMod (gcons C δ G)

{--- mutual recursive declarations: ---}

  data Mod : {C : Set} {G : Gr C} (R : RawMod G) → Set₁
  Located : {C : Set} (G : Gr C) {R : RawMod G} (M : Mod R) (∂ : C → Set) (x : X) → Set

{--- declarations above, definitions below ---}


  data Mod where
    mnil : Mod rnil
    mcons : {C D : Set} {G : Gr D} {δ : (C → D → Set)} {R : RawMod G} {xofc : C → X}
      (M : Mod R) (loc : (c : C) → Located G M (δ c) (xofc c)) → Mod (rcons R xofc)

  Located gnil M c x = ⊤
  Located (gcons C δ G) (mcons {xofc = xofc} M loc) ∂ x = (c : C) (m : ∂ c) → Σ (Located G M (δ c) x) (λ ℓ → (x , ℓ) == (xofc c , loc c))

open FixX
