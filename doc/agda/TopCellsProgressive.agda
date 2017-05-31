{-# OPTIONS --without-K --rewriting #-}

module TopCellsProgressive where

open import HoTT

module Verison1 where
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

module Version2 where
  data Gr : Set₁
  data Flt : Gr → Set₁

  data Gr where
    gnil : Gr
    gcons : (G : Gr) (f : Flt G) → Gr

  data Flt where
    fnil : Flt gnil
    fcons : {G : Gr} {f : Flt G} (δ : Set) → Flt G → Flt (gcons G f)

  module FixX (X : Set) where

    data RawMod : Gr → Set₁ where
      rnil : RawMod gnil
      rcons : {G : Gr} {f : Flt G} (R : RawMod G) (x : X) → RawMod (gcons G f)

    data Mod : {G : Gr} (R : RawMod G) → Set₁
    Located : {G : Gr} {R : RawMod G} (M : Mod R) (f : Flt G) (x : X) → Set

    data Mod where
      mnil : Mod rnil
      mcons : {G : Gr} {f : Flt G} {R : RawMod G} {x : X} (M : Mod R) → Located M f x → Mod (rcons {f = f} R x)

    Located mnil fnil x = ⊤
    Located {gcons G δ} {rcons R x0} (mcons M ℓ0) (fcons ∂ δ0) x = (Located M δ0 x) × ((m : ∂) → Σ (Located M δ x) (λ ℓ → (x , ℓ) == (x0 , ℓ0)))

  ○gr : Gr
  ○gr = gcons (gcons gnil fnil) (fcons Bool fnil)
