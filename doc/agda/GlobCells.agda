{-# OPTIONS --without-K --rewriting #-}

open import HoTT

module GlobCells where

data bd (τ : Set) (C : τ → Set) : Set where
  b0 : bd τ C
  bS : (t : τ) → C t → C t → bd τ C

record Complex : Set₁ where
  constructor MkComp
  field
    τ : Set
    C : τ → Set
    p : τ ≃ bd τ C

module _ (X : Set) (G : Complex) where
  open Complex G
  bdM : (t : bd τ C) (γ : τ → Set) (β : (t : τ) → C t → γ t) → Set
  bdM b0 γ β = X
  bdM (bS t x y) γ β = β t x == β t y
  record Mod : Set₁ where
    constructor MkMod
    field
      γ : τ → Set
      β : (t : τ) → C t → γ t
      pM : (t : τ) → γ t ≃ bdM (–> p t) γ β

{-- example --}

data τ : Set
data C0 : Set
data C1 : C0 → C0 → Set
data C2 : (C D : C0) → C1 C D → C1 C D → Set

data C0 where
  A B D : C0

data C1 where
  f g : C1 A B

data C2 where

data τ where
  t0 : τ
  t1 : C0 → C0 → τ
  t2 : (C D : C0) → C1 C D → C1 C D → τ

C : τ → Set
C t0 = C0
C (t1 a b) = C1 a b
C (t2 a b h k) = C2 a b h k

j : Complex
j = MkComp τ C (equiv into out zig zag) where
  into : τ → bd τ C
  into t0 = b0
  into (t1 x y) = bS t0 x y
  into (t2 C₁ D₁ x y) = bS (t1 C₁ D₁) x y
  out : bd τ C → τ
  out b0 = t0
  out (bS t0 x y) = t1 x y
  out (bS (t1 x x₁) x₂ x₃) = t2 x x₁ x₂ x₃
  out (bS (t2 z y e r) () q)
  zig : (b : bd τ C) → into (out b) == b
  zig b0 = idp
  zig (bS t0 x x₁) = idp
  zig (bS (t1 x x₁) x₂ x₃) = idp
  zig (bS (t2 C₁ D₁ x x₁) () x₃)
  zag : (b : τ) → out (into b) == b
  zag t0 = idp
  zag (t1 x x₁) = idp
  zag (t2 C₁ D₁ x x₁) = idp
