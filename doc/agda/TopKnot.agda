{-# OPTIONS --without-K --rewriting #-}

open import HoTT hiding (Bool ; true ; false ; _$_ ; Path)

module TopKnot where

data 𝟚 : Set where
  cod : 𝟚
  dom : 𝟚

record Bundle (C : Set) : Set₂ where
  constructor MkBundle
  field
    Bd : Set₁
    Cell : Set₁
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

record CellG {Bd : Set₁} {C : Set}  : Set₁ where
  field
    bd : Bd
    θ : C

First : (C : Set) → Bundle C
First C = MkBundle Bd Cell Mod Pathb Parts RealType Real where
  Bd : Set₁
  Bd = BdG (Lift ⊤) (λ _ → Lift ⊤)
  Cell = CellG {Bd} {C}
  Mod : (X : Set) → Set₁
  Mod X = Lift (C → X)
  Pathb = PathbG {Bd} {Cell} {λ _ _ → Lift ⊤}
  Parts = PathbG.parts
  RealType : {X : Set} (bd : Bd) (M : Mod X) → Set
  RealType bd M = ⊤
  Real : {X : Set} {bd : Bd} (M : Mod X) (π : Pathb bd) → RealType bd M
  Real M π = tt

Next : (C nC : Set) (b : Bundle C) → Bundle nC
Next C nC b = MkBundle nBd nCell nMod nPathb nParts nRealType nReal where
  open Bundle b

  nBd = BdG Bd Pathb

  nCell = CellG {nBd} {nC}

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
