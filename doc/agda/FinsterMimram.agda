{-# OPTIONS --without-K --rewriting #-}

module FinsterMimram where

open import HoTT
open import FinsterMimramBase


data Ty : {n : ℕ} → List Pd → Set
data Tm : {n : ℕ} → List Pd → Set

data Ty where
  ★ : ∀ {Δ n} → Ty {n} Δ
  _⇒_ : ∀ {Δ n} (t u : Tm {n} Δ) → Ty {S n} Δ

data Tm where
  Var : ∀ {Δ n} → (r : Ref n Δ) → Tm {n} Δ

RefTy : {Δ : List Pd} {n : ℕ} → Ref n Δ → Ty {n} Δ
RefTy {n = O} r = ★
RefTy {n = S n} r = Var (dom r) ⇒ Var (cod r)

data Of {n : ℕ} {Δ : List Pd} : Tm {n} Δ → Ty {n} Δ → Set where
  OfVar : (r : Ref n Δ) → Of (Var r) (RefTy r)

data WfTy {Δ : List Pd} : {n : ℕ} → Ty {n} Δ → Set where
  WfTy★ : WfTy {n = 0} ★
  WfTy⇒# : ∀ {n} {C D : Ty {n} Δ} {A B : Tm Δ} → Of A C → Of B D → C == D → WfTy (A ⇒ B)


RefTySynth : ∀ {Δ n} (r : Ref n Δ) → (of1 of2 : Of (Var r) (RefTy r)) → of1 == of2
RefTySynth r of1 of2 = {!!}

Typed : ∀ {Δ n} → (A : Ty {n} Δ) → Set
Typed {Δ} {n} A = Σ (Tm {n} Δ) (λ t → Of t A)

Typedπ₁Inj : ∀ {Δ n} → (A : Ty {n} Δ) (t u : Typed A) → fst t == fst u → t == u
Typedπ₁Inj A (fst₁ , snd₁) (.fst₁ , snd₂) idp = {!!}

OfSynthV : ∀ {Δ n} {A : Ty {n} Δ} → Typed A == Σ (Ref n Δ) (λ r → Of (Var r) (RefTy r))
OfSynthV = {!!}


OfSynth : ∀ {Δ n} {A : Ty {n} Δ} (t : Tm {n} Δ) → (of1 of2 : Of t A) → of1 == of2
OfSynth {A = .(RefTy r)} (Var r) (OfVar .r) of2 = OfUniq where
  OfUniq : OfVar r == of2
  OfUniq = {!!}


Wf⇒Same : ∀ {Δ n} {t u : Tm {n} Δ} {C1 C2 : Ty {n} Δ} (of1 : Of t C1) (of2 : Of u C1) (of3 : Of t C2) (of4 : Of u C2) → C1 == C2
Wf⇒Same = {!!}


WfSame : ∀ {Δ n} {A : Ty {n} Δ} (p q : WfTy A) → p == q
WfSame WfTy★ WfTy★ = idp
WfSame (WfTy⇒# of1 of2 idp) (WfTy⇒# of3 of4 idp) = {!!}

OfX : {Δ : List Pd} {n : ℕ} (r : Ref (S n) Δ) → RefTy (dom r) == RefTy (cod r)
OfX {n = O} r = idp
OfX {n = S n} r = ap2 (λ x y → Var x ⇒ Var y) (domLemma r) (codLemma r)

RefWf : {Δ : List Pd} {n : ℕ} (r : Ref n Δ) → WfTy (RefTy r)
RefWf {n = O} r = WfTy★
RefWf {n = S n} r = WfTy⇒# (OfVar (dom r)) (OfVar (cod r)) (OfX r)

OfWf : ∀ {n} → {Δ : List Pd} {M : Tm {n} Δ} {A : Ty Δ} → Of M A → WfTy A
OfWf (OfVar r) = RefWf r

postulate
  _~>_ : ∀ {n} {A : Set n} → A → A → Set

data Subst : (Δ : List Pd) (A : Set) → Set₁
getSubHead : {Δ : List Pd} {A : Set} → Subst Δ A → A


data Subst where
  snil :  {A : Set} (a : A) → Subst nil A
  scons :  {Δhd Δtl : List Pd} {A : Set} {a : A} (σtl : Subst Δtl A) (σhd : Subst Δhd (a ~> getSubHead σtl)) → Subst (pc Δhd :: Δtl) A

getSubHead (snil a) = a
getSubHead (scons {a = a} σtl σh) = a


record interp (Δ : List Pd) (X : Set) : Set₁ where
  field
    ity : ∀ {n} → Ty {n} Δ → Set
    itm : ∀ {n} → (t : Tm {n} Δ) (τ : Ty {n} Δ) → Of t τ → ity τ

interpTy : {Δ : List Pd} {n : ℕ} (X : Set) (σ : Subst Δ X)  (τ : Ty {n} Δ) (Y : Set) → Set₁
interpTm : {Δ : List Pd} {n : ℕ} (X : Set) (σ : Subst Δ X) (t : Tm {n} Δ) (Y : Set) (y : Y) → Set
interpRef : {Δ : List Pd} {n : ℕ} (X : Set) (σ : Subst Δ X) (r : Ref n Δ) (Y : Set) (y : Y) → Set

interpTy X σ ★ Y = X == Y
interpTy X σ (t ⇒ u) Y = Σ Set (λ C → Σ C (λ t0 → Σ C (λ u0 → interpTm X σ t C t0 × interpTm X σ u C u0 × Y == (t0 ~> u0))))
interpTm X σ (Var r) Y y = interpRef X σ r Y y
interpRef X σ r0 Y y =  Σ (Y ≃ X) (λ f → –> f y == getSubHead σ)
interpRef X (scons σtl σhd) (rtl r) Y y = interpRef X σtl r Y y
interpRef X (scons {a = a} σtl σhd) (rhd r) Y y = interpRef (a ~> getSubHead σtl) σhd r Y y
