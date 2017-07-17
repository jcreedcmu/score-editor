{-# OPTIONS --without-K --rewriting #-}

open import HoTT hiding (Bool ; true ; false ; _$_ ; Path)

module Asdf where

Pair : ∀ {n} → Set n → Set n
Pair X = X × X

Gr0 : Set₁
Gr0 = Set

Mod0 : (X : Set) → Gr0 → Set
Mod0 X C = C → X

Bd0 : Gr0 → Set
Bd0 G = Pair G

record Gr1 : Set₁ where
  constructor MkGr1
  field
    G0 : Gr0
    C1 : Bd0 G0 → Set

Dd1 : Gr1 → Set
Dd1 G1 = Bd0 G0 where open Gr1 G1

Mod1 : (X : Set) → Gr1 → Set
Mod1 X G1 = Σ (Mod0 X G0) (λ M0 → (δ : Bd0 G0) (c : C1 δ) → M0 (fst δ) == M0 (snd δ))  where open Gr1 G1

Path1 : (G1 : Gr1) → Bd0 (Gr1.G0 G1) → Set₁
Path1 G1 δ0 = (X : Set) (M : Mod1 X G1) → (fst M) (fst δ0) == (fst M) (snd δ0) where open Gr1 G1

Bd1 : Gr1 → Set₁
Bd1 G1 = Σ (Bd0 G0) (λ δ0 → Pair (Path1 G1 δ0)) where open Gr1 G1

record Gr2 : Set₁ where
  constructor MkGr2
  field
    G1 : Gr1
    C2 : Bd1 G1 → Set

Dd2 : Gr2 → Set₁
Dd2 G2 = Bd1 G1 where open Gr2 G2

Mod2 : (X : Set) → Gr2 → Set₁
Mod2 X G2 = Σ (Mod1 X G1) (λ M1 → (δ : Bd1 G1) (c : C2 δ) → fst (snd δ) X M1 == snd (snd δ) X M1) where open Gr2 G2

Path2 : (G2 : Gr2) → Dd2 G2 → Set₁
Path2 G2 δ1 = (X : Set) (M : Mod2 X G2) → fst (snd δ1) X (fst M) == snd (snd δ1) X (fst M) where open Gr2 G2

BdRight2 : (G2 : Gr2) (δ : Dd2 G2) → Set₁
BdRight2 G2 δ = Pair (Path2 G2 δ)

Bd2 : Gr2 → Set₁
Bd2 G2 = Σ (Dd2 G2) (BdRight2 G2)

{-----}
record Gr3 : Set₁ where
  constructor MkGr3
  field
    G2 : Gr2
    C3 : Σ (Dd2 G2) (BdRight2 G2) → Set

Dd3 : Gr3 → Set₁
Dd3 G3 = Σ (Dd2 G2) (BdRight2 G2) where open Gr3 G3

Mod3 : (X : Set) → Gr3 → Set₁
Mod3 X G3 = Σ (Mod2 X G2) (λ M2 → (δ : Bd2 G2) (c : C3 δ) → fst (snd δ) X M2 == snd (snd δ) X M2) where open Gr3 G3

PathRight3 : (G3 : Gr3) → Dd3 G3 → (X : Set) (M : Mod3 X G3) → Set
PathRight3 G3 δ2 X M = fst (snd δ2) X (fst M) == snd (snd δ2) X (fst M) where open Gr3 G3

BdRight3 : (G3 : Gr3) (δ : Dd3 G3) → Set₁
BdRight3 G3 δ = Pair ((X : Set) (M : Mod3 X G3) → PathRight3 G3 δ X M)

record Bundle : Set₂ where
  constructor MkBundle
  field
    Gr : Set₁
    Bd : Gr → Set₁
    Mod : (X : Set) → Gr → Set₁
    Path : (G : Gr) → Bd G → (X : Set) → Mod X G → Set

module Foo (β : Bundle) where
  open Bundle β
  σ : Gr → Set₁
  σ G = Σ (Bd G) (λ δ → Pair ((X : Set) (M : Mod X G) → Path G δ X M))
  record nGr : Set₁ where
    constructor MkGr
    field
      G : Gr
      C : σ G → Set
  nBd : nGr → Set₁
  nBd nG = σ G where open nGr nG
  nEq : (G : Gr) (X : Set) (M : Mod X G) (δ : σ G) → Set
  nEq G X M (_ , δ) = fst δ X M == snd δ X M
  nMod : Set → nGr → Set₁
  nMod X nG = Σ (Mod X G) (λ M → (δ : σ G) (c : C δ) → nEq G X M δ) where open nGr nG
  nPath : (nG : nGr) → nBd nG → (X : Set) → nMod X nG → Set
  nPath nG δ X (M , _) = nEq G X M δ where open nGr nG
  Next : Bundle
  Next = MkBundle nGr nBd nMod nPath

First : Bundle
First = MkBundle Set (λ _ → Lift ⊤) (λ X C → Lift (C → X)) (λ C δ X M → ⊤)

Second : Bundle
Second = Foo.Next First
