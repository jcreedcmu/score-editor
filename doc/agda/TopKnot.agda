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
    δ : C → Bd
    Mod : Set → Set₁
    Pathb : Bd → Set₁
    Parts : {bd : Bd} → Pathb bd → C → Set
    RealType : {X : Set} (bd : Bd) (M : Mod X) → Set
    Real : {X : Set} {bd : Bd} (M : Mod X) (π : Pathb bd) → RealType bd M

record PathbG {Bd : Set₁} {C : Set} {Path : Bd → (C → Set) → Set₁} (bd : Bd) : Set₁ where
  field
    parts : C → Set
    isPath : Path bd parts

record BdG (pBd : Set₁) (pPathb : pBd → Set₁) : Set₁ where
  field
    bd : pBd
    α β : pPathb bd

First : (C : Set) → Bundle C
First C =  MkBundle Bd δ Mod Pathb Parts RealType Real where
  Bd : Set₁
  Bd = BdG (Lift ⊤) (λ _ → Lift ⊤)
  δ = λ _ → record { bd = lift unit ; α = lift unit ; β = lift unit }
  Mod : (X : Set) → Set₁
  Mod X = Lift (C → X)
  Pathb = PathbG {Bd} {C} {λ _ _ → Lift ⊤}
  Parts = PathbG.parts
  RealType : {X : Set} (bd : Bd) (M : Mod X) → Set
  RealType bd M = ⊤
  Real : {X : Set} {bd : Bd} (M : Mod X) (π : Pathb bd) → RealType bd M
  Real M π = tt

NextBd : {C : Set} (b : Bundle C) → Set₁
NextBd b = BdG Bd Pathb where open Bundle b

Next : (C nC : Set) (b : Bundle C) (nδ : nC → NextBd b) → Bundle nC
Next C nC b nδ = MkBundle nBd nδ nMod nPathb nParts nRealType nReal where
  open Bundle b
  nBd = NextBd b
  nEq : {X : Set} (M : Mod X) (bd : nBd) → Set
  nEq M bd = Real M α == Real M β where open BdG bd

  nMod : (X : Set) → Set₁
  nMod X = Σ (Mod X) (λ M → (c : nC) → nEq M (nδ c))

  nPath : (bd : nBd) (θs : nC → Set) → Set₁
  nPath bd θs = (X : Set) (M : Mod X) → ((c : nC) → θs c → nEq M (nδ c)) → nEq M bd

  nPathb = PathbG {nBd} {nC} {nPath}
  nParts = PathbG.parts

  nRealType : {X : Set} (bd : nBd) (M : nMod X) → Set
  nRealType {X} bd (M , _) = nEq M bd

  nReal : {X : Set} {bd : nBd} (M : nMod X) (π : nPathb bd) → nRealType bd M
  nReal {X} {bd} (M , nM) π = isPath X M (λ c _ → nM c) where open PathbG π
