{-# OPTIONS --without-K --rewriting #-}

module TopCellsFix where

open import HoTT

record Gr : Set₁ where
  constructor MkGraph
  field
    𝕍 : Set
    𝔼 : 𝕍 → 𝕍 → Set

data const {A B : Set} : (A → B) → Set where
  /const : (b : B) → const  (λ _ → b)

data dconst {A : Set} {B : A → Set} : Π A B → Set where
  /dconst : (a : A) (b : (a : A) → B a) → dconst (λ x → b x)

module FixGr (X : Set) (G : Gr) where

{--- mutual recursive declarations: ---}

  open Gr G
  Mod : {n : ℕ} → Set
  Located : {n : ℕ} (M : Mod {n}) (w : 𝕍) (x : X) → Set

{--- declarations above, definitions below ---}

  Mod {0} = 𝕍 → X
  Mod {S n} = Σ (Mod {n}) (λ M → (w : 𝕍) → Σ X (Located {n} M w))

  Located {0} M w x = const (λ (vm : Σ 𝕍 (𝔼 w)) → M (fst vm))
  Located {S n} M w x = const {Σ 𝕍 (𝔼 w)} {B} (λ (vm : Σ 𝕍 (𝔼 w)) → foo vm) where
    B : Set
    B = {!!}
    foo : Σ 𝕍 (𝔼 w) → B
    foo v = {!snd M (fst v)!}
-- (v : 𝕍) (m : 𝔼 w v) → Σ (Located {n} (fst M) v x) (λ ℓ → (x , ℓ) == snd M v)

{-

Mod 1 == 𝕍 → X
Located 1 (M : Mod 1) w x == (v : 𝕍) (m : 𝔼 w v) → (x == M v)

Mod 2 == Σ (𝕍 → X) (λ M → (w : 𝕍) → Σ X (Located 1 M w))
Located 2 (M : Mod 2) w x == (v : 𝕍) (m : 𝔼 w v) → Σ (Located {1} (fst M) v x) (λ ℓ → (x , ℓ) == snd M v)


-}
