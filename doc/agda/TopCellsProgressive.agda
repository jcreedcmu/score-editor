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
  open FixX

  module _ where

    postulate  -- HIT
      ○ : Set

    module _ where

      postulate  -- HIT
        ○pt : ○
        ○path : ○pt == ○pt

    module ○Elim {P : ○ → Set}
      (pt* : P ○pt)
      (path* : pt* == pt* [ P ↓ ○path ]) where

      postulate  -- HIT
        f : Π (○) P
        pt-β : f ○pt ↦ pt*
      {-# REWRITE pt-β #-}

      postulate -- HIT
        path-β : apd f ○path ↦ path*
      {-# REWRITE path-β #-}

  ○-elim = ○Elim.f

  ●gr : Gr
  ●gr = gcons (gcons gnil fnil) (fcons Bool fnil)

  ○R : RawMod ○ ●gr
  ○R = rcons (rcons rnil ○pt) ○pt

  id↓ : {A C : Set} (a b : A) (c : C) (p : a == b) → c == c [ (λ _ → C) ↓ p ]
  id↓ a b c idp = idp

  ○M : Mod ○ ○R
  ○M = mcons (mcons mnil tt) (tt , (λ m → tt , (pair= ○path (id↓ ○pt ○pt tt ○path))))

  {--- Defining the circle as the thing whose homs into X are ●gr-models ---}

  postulate
    ● : Set
    ●! : (X : Set) → (Σ (RawMod X ●gr) (λ R → Mod X R)) ≃ (● → X)

  ●J1 : Σ (RawMod ● ●gr) (λ R → Mod ● R)
  ●J1 = <– (●! ●) (idf ●)

  ●R1 : RawMod ● ●gr
  ●R1 = fst ●J1

  ●M1 : Mod ● ●R1
  ●M1 = snd ●J1

  thm : ● ≃ ○
  thm = equiv into out zig zag where
    into : ● → ○
    into = –> (●! ○) mod where
      mod : Σ (RawMod ○ ●gr) (λ R → Mod ○ R)
      mod = ○R , ○M

    out : ○ → ●
    out = ○-elim {P = (λ _ → ●)} {!!} {!!}

    zig : (b : ○) → into (out b) == b
    zig = {!!}

    zag : (a : ●) → out (into a) == a
    zag = {!!}
