{-# OPTIONS --without-K --rewriting #-}

module TopCellsFix where

open import HoTT hiding ( _$_ ; north ; south ) renaming ( Type to _Type )


data _ble_ : Bool → Bool → Set where
  fblef : false ble false
  fblet : false ble true
  tblet : true ble true

{--- mutual recursive declarations: ---}

data Gr : Set
data Into : Gr → Set
data Compo : {G : Gr} (φg φf : Into G) → Set
CompoCompo : {G : Gr} {a b c : Into G} → Compo a b → Compo b c → Compo a c → Set

{--- declarations above, definitions below ---}

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

data Compo where
  cnil : Compo fnil fnil
  ccons : {G : Gr} {φf₁ φf₂ φg : Into G}
    {χ₁ : Compo φg φf₁} {χ₂ : Compo φg φf₂} {b₁ b₂ : Bool}
    (χf : Compo φf₁ φf₂) (le : b₁ ble b₂) (cc : CompoCompo χ₁ χf χ₂)
    → Compo (fcons φf₁ χ₁ b₁) (fcons φf₂ χ₂ b₂)

CompoCompo cnil cnil cnil = ⊤
CompoCompo a b c = {!!}


module GFixX (X : Set) where

{--- mutual recursive declarations: ---}

  Mod : Gr → Set
  data Located (x : X) : {G : Gr} (M : Mod G) (φ : Into G) → Set
  IdMod : (x : X) {G : Gr} → Mod G
  IdAt : (x : X) {G : Gr} (φ : Into G) → Located x (IdMod x {G}) φ
  Res : {x : X} {G : Gr} {φf φg : Into G} (χ : Compo φg φf) {M : Mod G} → Located x M φf → Located x M φg
  CcThm : {G : Gr} {a b c : Into G} {f : Compo a b} {g : Compo b c} {h : Compo a c}
    {x : X} {M : Mod G} {ℓ : Located x M c}
    → CompoCompo f g h → Res f (Res g ℓ) == Res h ℓ
  ResThm : {x : X} {G : Gr} {φf φg : Into G} (χ : Compo φg φf) → Res χ (IdAt x φf) == IdAt x φg

{--- declarations above, definitions below ---}

  Mod gnil = ⊤
  Mod (gcons G φ) = Σ (Mod G) (λ M → Σ X (λ x → Located x M φ))

  data Located (x : X) where
    ℓnil : Located x tt fnil
    ℓno : {G : Gr} {M : Mod G} {φf φg : Into G} {χ : Compo φg φf} {pf : Σ X (λ x → Located x M φg)}
      → Located x M φf → Located x (M , pf) (fcons φf χ false)
    ℓyes : {G : Gr} (M : Mod G) {φf φg : Into G} {χ : Compo φg φf}
      (ℓ : Located x M φf) → Located x (M , x , Res χ ℓ) (fcons φf χ true)

  Res cnil ℓnil = ℓnil
  Res (ccons χ fblef cc) (ℓno ℓ) = ℓno (Res χ ℓ)
  Res (ccons χ fblet cc) (ℓyes M ℓ) = ℓno (Res χ ℓ)
  Res {x = x} {G = gcons G φg} (ccons {φf₁ = φf₁} {χ₁ = χ₁} {χ₂} χ tblet cc) (ℓyes M ℓ) =
    coe eq (ℓyes {G = G}  M {χ = χ₁} (Res χ ℓ)) where
      eq = ap (λ z → Located x (M , x , z) (fcons φf₁ χ₁ (inl unit))) (CcThm {f = χ₁} cc)

  CcThm = {!!}


  IdMod x {gnil} = tt
  IdMod x {gcons G φ} = (IdMod x {G}) , (x , IdAt x φ)

  IdAt x {gnil} fnil = ℓnil
  IdAt x {gcons G φg} (fcons φf χ false) = ℓno (IdAt x {G} φf)
  IdAt x {gcons G φg} (fcons φf χ true) =
    coe eq (ℓyes {G = G} (IdMod x {G}) {φf} {φg} {χ} (IdAt x {G} φf)) where
    eq = ap (λ z → Located x (IdMod x , x , z) (fcons φf χ (inl unit))) (ResThm χ)

  ResThm = {!!}
