{-# OPTIONS --without-K --rewriting #-}

open import HoTT hiding (ℤ)

module TopCellsInterleave where

data 𝟚 : Set where
  cod : 𝟚
  dom : 𝟚

record Gr : Set₁ where
  constructor MkG
  field
    C : ℕ → Set
    δ : {n : ℕ} → C (S n) → C n → 𝟚 → Set


module _  (G : Gr) where
  open Gr G

  Mod0 : (X : Set) → Set
  Mod0 X = C 0 → X

{- stuff for 1-cells -}
  Basic1 : C 0 → C 0 → C 1 → Set
  Basic1 x y f = δ f x dom × δ f y cod

  record Cell1 : Set where
     field
       x1 : C 0
       y1 : C 0
       f1 : C 1
       B1 : Basic1 x1 y1 f1

  Eq1 : (X : Set) (M0 : Mod0 X) → Cell1 → Set
  Eq1 X M0 c1 = M0 (Cell1.x1 c1) == M0 (Cell1.y1 c1)

  Mod1 : (X : Set) → Set
  Mod1 X = Σ (Mod0 X) (λ M0 → (c1 : Cell1) → Eq1 X M0 c1)

  Path1 : C 0 → C 0 → (Cell1 → Set) → Set₁
  Path1 x y fs = (X : Set) (M0 : Mod0 X) → ((c1 : Cell1) → fs c1 → Eq1 X M0 c1) → M0 x == M0 y

  record Pathb1 (A B : C 0) : Set₁ where
    constructor MkPathb1
    field
      parts1 : Cell1 → Set
      isPath1 : Path1 A B parts1

  Real1 : {X : Set} {x y : C 0} (M : Mod1 X) → Pathb1 x y → (fst M) x == (fst M) y
  Real1 {X} (M0 , M1) z = isPath1 X M0 (λ c1 _ → M1 c1) where open Pathb1 z

{----------- stuff for 2-cells ------------}
  Related2 : C 2 → (Cell1 → Set) → 𝟚 → Set
  Related2 α fs bb = (c1 : Cell1) → fs c1 → δ α (Cell1.f1 c1) bb

  record Bd2 : Set₁ where
    field
      x2 y2 : C 0
      f2 g2 : Pathb1 x2 y2

  Basic2 : (bd : Bd2) → C 2 → Set
  Basic2 bd α = Related2 α (Pathb1.parts1 (Bd2.f2 bd)) dom × Related2 α (Pathb1.parts1 (Bd2.g2 bd)) cod

  record Cell2 : Set₁ where
    field
      bd2 : Bd2
      α2 : C 2
      B2 : Basic2 bd2 α2

  Eq2 : (X : Set) (M : Mod1 X) → Cell2 → Set
  Eq2 X M@(M0 , M1) c2 = Real1 M f2 == Real1 M g2 where open Cell2 c2 ; open Bd2 bd2

  Mod2 : (X : Set) → Set₁
  Mod2 X = Σ (Mod1 X) (λ M1 → (c2 : Cell2) → Eq2 X M1 c2)

  Path2 : (bd2 : Bd2) (αs : Cell2 → Set) → Set₁
  Path2 bd2 αs = (X : Set) (M : Mod1 X) → ((c2 : Cell2) → αs c2 → Eq2 X M c2) → Real1 M f2 == Real1 M g2 where open Bd2 bd2

  record Pathb2 (bd2 : Bd2) : Set₁ where
    constructor MkPathb2
    field
      parts2 : Cell2 → Set
      isPath2 : Path2 bd2 parts2

  Real2 : {X : Set} {bd2 : Bd2} (M : Mod2 X) → Pathb2 bd2 → Real1 (fst M) (Bd2.f2 bd2) == Real1 (fst M) (Bd2.g2 bd2)
  Real2 {X} {bd2} (M1 , M2) π = isPath2 X M1 (λ c2 _ → M2 c2) where open Pathb2 π

{----------- stuff for 3-cells ------------}

  Related3 : C 3 → (Cell2 → Set) → 𝟚 → Set₁
  Related3 θ αs bb = (c2 : Cell2) → αs c2 → δ θ (Cell2.α2 c2) bb

  record Bd3 : Set₁ where
    field
      bd2 : Bd2
      α β : Pathb2 bd2

  Basic3 : (bd : Bd3) → C 3 → Set₁
  Basic3 bd θ = Related3 θ (Pathb2.parts2 α) dom × Related3 θ (Pathb2.parts2 β) cod where open Bd3 bd

  record Cell3 : Set₁ where
    field
      bd : Bd3
      θ : C 3
      B : Basic3 bd θ

  Eq3 : (X : Set) (M : Mod2 X) → Cell3 → Set
  Eq3 X M c3 = Real2 M α == Real2 M β where open Cell3 c3 ; open Bd3 bd

  Mod3 : (X : Set) → Set₁
  Mod3 X = Σ (Mod2 X) (λ M2 → (c3 : Cell3) → Eq3 X M2 c3)

  Path3 : (bd : Bd3) (θs : Cell3 → Set) → Set₁
  Path3 bd θs = (X : Set) (M : Mod2 X) → ((c3 : Cell3) → θs c3 → Eq3 X M c3) → Real2 M α == Real2 M β where open Bd3 bd

  record Pathb3 (bd3 : Bd3) : Set₁ where
    constructor MkPathb3
    field
      parts3 : Cell3 → Set
      isPath3 : Path3 bd3 parts3

  Real3 : {X : Set} {bd3 : Bd3} (M : Mod3 X) → Pathb3 bd3 → Real2 (fst M) (Bd3.α bd3) == Real2 (fst M) (Bd3.β bd3)
  Real3 {X} {bd3} (M2 , M3) π = isPath3 X M2 (λ c3 _ → M3 c3) where open Pathb3 π
