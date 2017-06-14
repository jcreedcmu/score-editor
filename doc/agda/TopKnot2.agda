{-# OPTIONS --without-K --rewriting #-}

open import HoTT hiding (Bool ; true ; false ; _$_ ; Path)

module TopKnot2 where

Pair : ∀ {n} → Set n → Set n
Pair X = X × X

record Bundle : Set₂ where
  constructor MkBundle
  field
    Gr : Set₁
    σ : Gr → Set₁
    Mod : (X : Set) → Gr → Set₁
    Eq : (G : Gr) (X : Set) (M : Mod X G) (δ : σ G) → Set

module Foo (β : Bundle) where
  open Bundle β

  record nGr : Set₁ where
    constructor MkGr
    field
      G : Gr
      C : σ G → Set
  nBd : nGr → Set₁
  nBd nG = σ G where open nGr nG
  nMod : Set → nGr → Set₁
  nMod X nG = Σ (Mod X G) (λ M → (δ : σ G) (c : C δ) → Eq G X M δ) where open nGr nG
  nPath : (nG : nGr) → nBd nG → (X : Set) → nMod X nG → Set
  nPath nG δ X (M , _) = Eq G X M δ where open nGr nG
  nσ : nGr → Set₁
  nσ nG = Σ (nBd nG) (λ δ → Pair ((X : Set) (M : nMod X nG) → nPath nG δ X M))
  nEq : (nG : nGr) (X : Set) (M : nMod X nG) (δ : nσ nG) → Set
  nEq nG X M (_ , δ) = fst δ X M == snd δ X M

First : Bundle
First = MkBundle (Lift ⊤) (λ _ → Lift ⊤) (λ _ _ → Lift ⊤) (λ _ X _ _ → X)
