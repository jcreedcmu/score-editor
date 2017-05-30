{-# OPTIONS --without-K --rewriting #-}

module TopCellsFix where

open import HoTT hiding ( _$_ ; north ; south ) renaming ( Type to _Type )

record Gr : Set₁ where
  constructor MkGraph
  field
    𝕍 : Set
    𝔼 : 𝕍 → 𝕍 → Set

{--- mutual recursive declarations: ---}

module FixGr (X : Set) (G : Gr) where
  open Gr G
  Mod : {n : ℕ} → Set
  data Located (x : X) : {n : ℕ} (M : Mod {n}) (w : 𝕍) → Set

{--- declarations above, definitions below ---}

  Mod {O} = 𝕍 → X
  Mod {S n} = Σ (Mod {n}) (λ M → (v : 𝕍) → Σ X (λ x → Located x M v))

  data Located (x : X) where
    ℓ0 : {M : Mod {0}} {w : 𝕍} → ((v : 𝕍) → 𝔼 w v → M v == x) → Located x {0} M w
    ℓn : {n : ℕ} {M : Mod {S n}} {w : 𝕍} →
      ((v : 𝕍) (m : 𝔼 w v) → Σ (Located x {n} (fst M) v) (λ ℓ → (x , ℓ) == snd M v)) →
      Located x {S n} M w
