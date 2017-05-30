{-# OPTIONS --without-K --rewriting #-}

module TopCellsFix where

open import HoTT

record Gr : Set₁ where
  constructor MkGraph
  field
    𝕍 : Set
    𝔼 : 𝕍 → 𝕍 → Set

{--- mutual recursive declarations: ---}

module FixGr (X : Set) (G : Gr) where
  open Gr G
  Mod : {n : ℕ} → Set
  Located : {n : ℕ} (M : Mod {n}) (w : 𝕍) (x : X) → Set

{--- declarations above, definitions below ---}

  Mod {0} = ⊤
  Mod {S n} = Σ (Mod {n}) (λ M → (v : 𝕍) → Σ X (Located M v))

  Located {0} M w x = ⊤
  Located {S n} M w x = (v : 𝕍) (m : 𝔼 w v) → Σ (Located (fst M) v x) (λ ℓ → (x , ℓ) == snd M v)
