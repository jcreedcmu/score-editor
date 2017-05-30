{-# OPTIONS --without-K --rewriting #-}

module TopCellsFix where

open import HoTT hiding ( _$_ ; north ; south ) renaming ( Type to _Type )


data Gr : Set
data Flt : Gr → Set

data Gr where
  gnil : Gr
  gcons : (G : Gr) → Flt G → Gr

data Flt where
  fnil : Flt gnil
  -- φf is the φ of the filter we're inductively building.
  -- φg is the filter attached to the current node of the graph G
  fcons : {G : Gr} ({φg} φf : Flt G) → Bool → Flt (gcons G φg)

module GFixX (X : Set) where
  Mod : Gr → Set
  data Located (x : X) : {G : Gr} (M : Mod G) (φ : Flt G) → Set
  IdAt : (x : X) {G : Gr} (M : Mod G) (φ : Flt G) → Located x M φ

  Mod gnil = ⊤
  Mod (gcons G φ) = Σ (Mod G) (λ M → Σ X (λ x → Located x M φ))

  data Located (x : X) where
    ℓnil :  Located x tt fnil
    ℓno : {G : Gr} {M : Mod G} {φf φg : Flt G} {pf : Σ X (λ x → Located x M φg)}
      → Located x M φf → Located x (M , pf) (fcons φf false)
    ℓyes : {G : Gr} {M : Mod G} {φf φg : Flt G}
      → Located x M φf → Located x (M , x , IdAt x M φg) (fcons φf true)

  IdAt x {gnil} unit fnil = ℓnil
  IdAt x {gcons G φg} (M , ℓ) (fcons φf false) = ℓno {!snd ℓ!}
  IdAt x {gcons G φg} (M , ℓ) (fcons φf true) = {!ℓyes ?!}

-- Σ X (λ x → Located x M φg)
