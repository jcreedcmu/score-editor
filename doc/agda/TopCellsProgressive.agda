{-# OPTIONS --without-K --rewriting #-}

module TopCellsProgressive where

open import HoTT

data Gr : (C : Set) → Set₁ where
  gnil : Gr ⊤
  gcons : (C {D} : Set) (δ : (C → D → Set)) → Gr D → Gr C

module FixX (X : Set) where

{--- mutual recursive declarations: ---}

  Mod : {C : Set} (G : Gr C) → Set
  Located : {C : Set} (G : Gr C) (M : Mod G) (x : C → Set) (x : X) → Set

{--- declarations above, definitions below ---}

  Mod gnil = ⊤
  Mod (gcons C δ G) = Σ (Mod G) (λ M → (c : C) → Σ X (Located G M (δ c)))

  Located gnil M c x = ⊤
  Located (gcons C δ G) M ∂ x = (c : C) (m : ∂ c) → Σ (Located G (fst M) (δ c) x) ((λ ℓ → (x , ℓ) == snd M c))
