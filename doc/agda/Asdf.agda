{-# OPTIONS --without-K --rewriting #-}

open import HoTT hiding (Bool ; true ; false ; _$_ ; Path)

module Asdf where

data 𝟚 : Set where
  cod : 𝟚
  dom : 𝟚

record Bundle (C : Set) : Set₂ where
  constructor MkBundle
  field
    Bd : Set₁
    Cell : Set₁
    Get : Cell → C
    Mod : Set → Set₁
    Pathb : Bd → Set₁
    Parts : {bd : Bd} → Pathb bd → Cell → Set
    RealType : {X : Set} (bd : Bd) (M : Mod X) → Set
    Real : {X : Set} {bd : Bd} (M : Mod X) (π : Pathb bd) → RealType bd M

record PathbG {Bd : Set₁} {Cell : Set₁} {Path : Bd → (Cell → Set) → Set₁} (bd : Bd) : Set₁ where
  field
    parts : Cell → Set
    isPath : Path bd parts

record BdG (pBd : Set₁) (pPathb : pBd → Set₁) : Set₁ where
  field
    bd : pBd
    α β : pPathb bd

record CellG {Bd : Set₁} {C : Set} {Basic : Bd → C → Set₁} : Set₁ where
  field
    bd : Bd
    θ : C
    B : Basic bd θ

First : Bundle ⊤
First =
  MkBundle (Lift ⊤) (Lift ⊤) (λ _ → tt) (λ _ → Lift ⊤)
    (λ _ → Lift ⊤) (λ _ _ → ⊤) (λ _ _ → ⊤) (λ _ _ → tt)

Next : (C nC : Set) (b : Bundle C) (nδ : nC → C → 𝟚 → Set) → Bundle nC
Next C nC b δ = MkBundle nBd nCell nGet nMod nPathb nParts nRealType nReal where
  open Bundle b
  nRelated : nC → (Cell → Set) → 𝟚 → Set₁
  nRelated θ αs bb = (c : Cell) → αs c → δ θ (Get c) bb

  nBd = BdG Bd Pathb

  nBasic : nBd → nC → Set₁
  nBasic bd θ = nRelated θ (Parts α) dom × nRelated θ (Parts β) cod where open BdG bd

  nCell = CellG {nBd} {nC} {nBasic}
  nGet = CellG.θ

  nEq : {X : Set} (M : Mod X) (bd : nBd) → Set
  nEq M bd = Real M α == Real M β where open BdG bd

  nMod : (X : Set) → Set₁
  nMod X = Σ (Mod X) (λ M → (c : nCell) → nEq M (CellG.bd c))

  nPath : (bd : nBd) (θs : nCell → Set) → Set₁
  nPath bd θs = (X : Set) (M : Mod X) → ((c : nCell) → θs c → nEq M (CellG.bd c)) → nEq M bd

  nPathb = PathbG {nBd} {nCell} {nPath}
  nParts = PathbG.parts

  nRealType : {X : Set} (bd : nBd) (M : nMod X) → Set
  nRealType {X} bd (M , _) = nEq M bd

  nReal : {X : Set} {bd : nBd} (M : nMod X) (π : nPathb bd) → nRealType bd M
  nReal {X} {bd} (M , nM) π = isPath X M (λ c _ → nM c) where open PathbG π
