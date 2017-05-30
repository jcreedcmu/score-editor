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
  Mod {S n} = Σ (Mod {n}) (λ M → (w : 𝕍) → Σ X (Located {n} M w))

  Located {0} M w x = ⊤
  Located {S n} M w x = (v : 𝕍) (m : 𝔼 w v) → Σ (Located {n} (fst M) v x) (λ ℓ → (x , ℓ) == snd M v)

{-

Mod 1 == 𝕍 → X
Located 1 (M : Mod 1) w x == (v : 𝕍) (m : 𝔼 w v) → (x == M v)

Mod 2 == Σ (𝕍 → X) (λ M → (w : 𝕍) → Σ X (Located 1 M w))
Located 2 (M : Mod 2) w x == (v : 𝕍) (m : 𝔼 w v) → Σ (Located {1} (fst M) v x) (λ ℓ → (x , ℓ) == snd M v)


-}
