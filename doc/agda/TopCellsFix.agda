{-# OPTIONS --without-K --rewriting #-}

module TopCellsFix where

open import HoTT hiding ( _$_ ; north ; south ) renaming ( Type to _Type )


data Gr : Set
data Into : Gr → Set
data Compo : {G : Gr} (φg φf : Into G) → Set

data Gr where
  gnil : Gr
  gcons : (G : Gr) → Into G → Gr

data Into where
  fnil : Into gnil
  -- φf is the φ of the homset we're inductively building.
  -- φg is the homset attached to the current node of the graph G
  fcons : {G : Gr} ({φg} φf : Into G) (χ : Compo φg φf) (b : Bool) → Into (gcons G φg)

-- In a more categorified world this might look like
--  fcons : {G : Gr} ({φg} φf : Into G) (X : Set) → Compo X φg φf → Into (gcons G φg)

data _ble_ : Bool → Bool → Set where
  fblef : false ble false
  *blet : (x : Bool) → x ble true

data Compo where
  cnil : Compo fnil fnil
  ccons : {G : Gr} {φf₁ φg φf₂ : Into G}
    {χ₁ : Compo φg φf₁} {χ₂ : Compo φg φf₂} {b₁ b₂ : Bool}
    (χf : Compo φf₁ φf₂) → b₁ ble b₂ → Compo (fcons φf₁ χ₁ b₁) (fcons φf₂ χ₂ b₂)
-- XXX: can I define
-- CompoCompo : Compo a b → Compo b c → Compo a c
-- and replace χ₂ with CompoCompo χ₁ χf
-- ? Doesn't matter for now, since I only have Bool not Set and Compo proofs are essentially identical, I think.

module GFixX (X : Set) where
  Mod : Gr → Set
  data Located (x : X) : {G : Gr} (M : Mod G) (φ : Into G) → Set
  IdMod : (x : X) {G : Gr} → Mod G
  IdAt : (x : X) {G : Gr} (φ : Into G) → Located x (IdMod x {G}) φ
  Res : {x : X} {G : Gr} {φf φg : Into G} (χ : Compo φg φf) {M : Mod G} → Located x M φf → Located x M φg
{---}
  Mod gnil = ⊤
  Mod (gcons G φ) = Σ (Mod G) (λ M → Σ X (λ x → Located x M φ))

  data Located (x : X) where
    ℓnil : Located x tt fnil
    ℓno : {G : Gr} {M : Mod G} {φf φg : Into G} {χ : Compo φg φf} {pf : Σ X (λ x → Located x M φg)}
      → Located x M φf → Located x (M , pf) (fcons φf χ false)
    ℓyes : {G : Gr} {M : Mod G} {φf φg : Into G} {χ : Compo φg φf}
      (ℓ : Located x M φf) → Located x (M , x , Res χ ℓ) (fcons φf χ true)

  Res cnil ℓnil = ℓnil
  Res {φf = .(fcons _ _ false)} {.(fcons _ _ (inr unit))} (ccons χ fblef) (ℓno ℓ) = ℓno (Res χ ℓ)
  Res {φf = .(fcons _ _ true)} {.(fcons _ _ false)} (ccons χ (*blet false)) (ℓyes ℓ) = ℓno (Res χ ℓ)
  Res {φf = .(fcons _ _ true)} {.(fcons _ _ true)} (ccons χ (*blet true)) (ℓyes ℓ) = {!!}



  IdMod x {gnil} = tt
  IdMod x {gcons G φ} = (IdMod x {G}) , (x , IdAt x φ)

  IdAt x {gnil} fnil = ℓnil
  IdAt x {gcons G φg} (fcons φf χ false) = ℓno (IdAt x {G} φf)
  IdAt x {gcons G φg} (fcons φf χ true) = {!!}

  -- IdAt x {gnil} unit fnil = ℓnil
  -- IdAt x {gcons G φg} (M , ℓ) (fcons φf χ false) = ℓno {!snd ℓ !}
  -- IdAt x {gcons G φg} (M , ℓ) (fcons φf χ true) = {!ℓyes ?!}

-- Σ X (λ x → Located x M φg)
