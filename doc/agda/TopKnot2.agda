{-# OPTIONS --without-K --rewriting #-}

open import HoTT hiding (Bool ; true ; false ; _$_ ; Path)

module TopKnot2 where

Pair : ∀ {n} → Set n → Set n
Pair X = X × X

record Bundle : Set₂ where
  constructor MkBundle
  field
    Gr : Set₁
    Bd : Gr → Set₁
    Mod : (X : Set) → Gr → Set₁
    Eq : (G : Gr) (δ : Bd G) (X : Set) (M : Mod X G) → Set

module Foo (β : Bundle) where
  open Bundle β

  record nGr : Set₁ where
    constructor MkGr
    field
      G : Gr
      C : Bd G → Set
  pBd : nGr → Set₁
  pBd nG = Bd G where open nGr nG
  nMod : Set → nGr → Set₁
  nMod X nG = Σ (Mod X G) (λ M → (δ : Bd G) (c : C δ) → Eq G δ X M) where open nGr nG
  pEq : (nG : nGr) → pBd nG → (X : Set) → nMod X nG → Set
  pEq nG δ X (M , _) = Eq G δ X M where open nGr nG
  nBd : nGr → Set₁
  nBd nG = Σ (pBd nG) (λ δ → Pair ((X : Set) (M : nMod X nG) → pEq nG δ X M))
  nEq : (nG : nGr) (X : Set) (M : nMod X nG) (δ : nBd nG) → Set
  nEq nG X M (_ , δ) = fst δ X M == snd δ X M

First : Bundle
First = MkBundle (Lift ⊤) (λ _ → Lift ⊤) (λ _ _ → Lift ⊤) (λ _ _ X _ → X)
