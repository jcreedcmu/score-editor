{-# OPTIONS --without-K --rewriting #-}

module TopCellsProgressive where

open import HoTT

data Gr : (C : Set) → Set₁ where
  gnil : Gr ⊤
  gcons : (C {D} : Set) (δ : (C → D → Set)) → Gr D → Gr C

module FixX (X : Set) where

{--- mutual recursive declarations: ---}

  Mod : {C : Set} (G : Gr C) → Set
  Located : {C : Set} (G : Gr C) (M : Mod G) (∂ : C → Set) (x : X) → Set

{--- declarations above, definitions below ---}

  Mod gnil = ⊤
  Mod (gcons C δ G) = Σ (Mod G) (λ M → (c : C) → Σ X (Located G M (δ c)))

  Located gnil M c x = ⊤
  Located (gcons C δ G) M ∂ x = (c : C) (m : ∂ c) → Σ (Located G (fst M) (δ c) x) ((λ ℓ → (x , ℓ) == snd M c))
open FixX

{--- circle graph ---}

●gr0 : Gr ⊤
●gr0 = gcons ⊤ (λ _ _ → ⊤) gnil

●gr1 : Gr ⊤
●gr1 = gcons ⊤ (λ tt b → Bool) (gcons ⊤ (λ _ _ → ⊤) gnil)

●gr : Gr ⊤
●gr = ●gr1

{--- Defining the circle as the thing whose homs into X are ●gr-models ---}

postulate
  ● : Set
  ●! : (X : Set) → Mod X ●gr ≃ (● → X)

{--- the usual HIT circle ---}

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

{--- Try to prove them equiv ---}

id↓ : {A C : Set} (a b : A) (c : C) (p : a == b) → c == c [ (λ _ → C) ↓ p ]
id↓ a b c idp = idp

●mod1 : Mod ● ●gr
●mod1 = <– (●! ●) (idf ●)

●mod0 : Mod ● ●gr0
●mod0 = fst ●mod1

●loc1 : Σ ● (Located ● ●gr0 ●mod0 (λ b → Bool))
●loc1 = snd ●mod1 tt

●loc0 : Σ ● (Located ● gnil tt (λ _ → ⊤))
●loc0 = snd ●mod0 tt

thm : ● ≃ ○
thm = equiv into out zig zag where
  into : ● → ○
  into = –> (●! ○) mod where
    mod : Mod ○ ●gr
    mod = (tt , (λ tt → ○pt , tt)) , (λ tt → ○pt , (λ tt b → tt , (pair= ○path (id↓ ○pt ○pt tt ○path))))

  out : ○ → ●
  out = ○-elim {P = (λ _ → ●)} (fst ●loc0) {!ap fst (snd (snd ●loc1 tt true)) ∙ ! (ap fst (snd (snd ●loc1 tt false)))!}

  zig : (b : ○) → into (out b) == b
  zig = {!!}

  zag : (a : ●) → out (into a) == a
  zag = {!!}
