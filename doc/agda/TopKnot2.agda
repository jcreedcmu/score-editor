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

module _Next (β : Bundle) where
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
  nEq : (nG : nGr) (δ : nBd nG) (X : Set) (M : nMod X nG) → Set
  nEq nG (_ , δ) X M = fst δ X M == snd δ X M

  Next : Bundle
  Next = MkBundle nGr nBd nMod nEq

open _Next using (Next)

L-1 : Bundle
L-1 = MkBundle (Lift ⊤) (λ _ → Lift ⊤) (λ _ _ → Lift ⊤) (λ _ _ X _ → X)

L0 = Next L-1
L1 = Next L0

-- example

data 𝕍 : Set where
  v1 v2 : 𝕍

data 𝔼 : (x y : 𝕍) → Set where
  e : 𝔼 v1 v2

Gr0 = Bundle.Gr L0
Gr1 = Bundle.Gr L1
Mod1 = Bundle.Mod L1

GetVertType : (G : Gr0) → Set
GetVertType G = _Next.nGr.C G (lift unit)
SelfMod : (G : Gr0) → _Next.nMod L-1 (GetVertType G) G
SelfMod G = (lift unit) , (λ δ c → c)
GetVert1 : (G : Gr0) → Bundle.Bd L0 G → GetVertType G
GetVert1 G δ = fst (snd δ) (GetVertType G) (SelfMod G)
GetVert2 : (G : Gr0) → Bundle.Bd L0 G → GetVertType G
GetVert2 G δ = snd (snd δ) (GetVertType G) (SelfMod G)

IG0 : Gr0
IG0 = _Next.MkGr (lift unit) (λ _ → 𝕍)
IG1 : Gr1
IG1 = _Next.MkGr IG0 (λ δ → 𝔼 (GetVert1 IG0 δ) (GetVert2 IG0 δ))
IBd0 = Bundle.Bd L0 IG0
IC1 = _Next.nGr.C IG1
IEq0 = Bundle.Eq L0 IG0

record IMod (X : Set) : Set where
  constructor MkIMod
  field
    x y : X
    p : x == y

into : (X : Set) → Mod1 X IG1 → IMod X
into X ((_ , M0) , M1) = MkIMod (M0 (lift tt) v1) (M0 (lift tt) v2) (M1 δ e) where
  δ : IBd0
  δ = (lift unit) , ((λ X' M' → snd M' (lift tt) v1) , (λ X' M' → snd M' (lift tt) v2))


out : (X : Set) → IMod X → Mod1 X IG1
out X (MkIMod x y p) = (lift unit , (λ _ c0 → f0 c0)) , f1 where
  f0 : 𝕍 → X
  f0 v1 = x
  f0 v2 = y
  f1 : (δ : IBd0) (c1 : IC1 δ) → IEq0 δ X (lift unit , (λ _ c → f0 c))
  f1 δ c1 = {!IEq0 δ X (lift unit , (λ _ → f0))!}

-- have:
-- 𝔼 (fst (snd δ) 𝕍 (lift unit , (λ δ₁ c → c)))
-- (snd (snd δ) 𝕍 (lift unit , (λ δ₁ c → c)))

-- fst (snd δ) X (lift unit , (λ _ → f0)) ==
-- snd (snd δ) X (lift unit , (λ _ → f0))
