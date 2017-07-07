{-# OPTIONS --without-K --rewriting #-}

module FinsterMimram where

open import HoTT

data Pd : Set where
  pc : List Pd → Pd

data Ref : ℕ → List Pd → Set where
  r0 : {Δ : List Pd} →  Ref 0 Δ
  rtl : {n : ℕ} {Δ : Pd} {Δs : List Pd} → Ref n Δs → Ref n (Δ :: Δs)
  rhd : {n : ℕ} {Δs1 Δs2 : List Pd} → Ref n Δs1 → Ref (S n) ((pc Δs1) :: Δs2)

dom : {n : ℕ} {Δ : List Pd} → Ref (S n) Δ → Ref n Δ
dom {0} (rhd _) = r0
dom {S n} (rhd m) = rhd (dom m)
dom {n} (rtl m) = rtl (dom m)

cod : {n : ℕ} {Δ : List Pd} → Ref (S n) Δ → Ref n Δ
cod {0} (rhd _) = rtl r0
cod {S n} (rhd m) = rhd (cod m)
cod {n} (rtl m) = rtl (cod m)

domLemma : {n : ℕ} {Δ : List Pd} (r : Ref (S (S n)) Δ) → dom (dom r) == dom (cod r)
domLemma {0} (rtl r) = ap rtl (domLemma r)
domLemma {S n} (rtl r) = ap rtl (domLemma r)
domLemma {O} (rhd r) = idp
domLemma {S n} (rhd r) = ap rhd (domLemma r)

codLemma : {n : ℕ} {Δ : List Pd} (r : Ref (S (S n)) Δ) → cod (dom r) == cod (cod r)
codLemma {0} (rtl r) = ap rtl (codLemma r)
codLemma {S n} (rtl r) = ap rtl (codLemma r)
codLemma {O} (rhd r) = idp
codLemma {S n} (rhd r) = ap rhd (codLemma r)

data Ty : {n : ℕ} → List Pd → Set
data Tm : {n : ℕ} → List Pd → Set
data Subst : List Pd → List Pd → Set
subConcat : ∀ {Γ Δ Ξ} → Subst Δ Γ → Subst Γ Ξ → Subst Δ Ξ
subTy : ∀ {Γ Δ n} → Subst Δ Γ → (A : Ty {n} Γ) → Ty {n} Δ
subTm : ∀ {Γ Δ n} → Subst Δ Γ → (A : Tm {n} Γ) → Tm {n} Δ
subRef : ∀ {Γ Δ n} → Subst Δ Γ → (A : Ref n Γ) → Tm {n} Δ

data Ty where
  ★ : ∀ {Δ n} → Ty {n} Δ
  _⇒_ : ∀ {Δ n} (t u : Tm {n} Δ) → Ty {S n} Δ

data Tm where
  Var : ∀ {Δ n} → (r : Ref n Δ) → Tm {n} Δ
  Coh : ∀ {Γ Δ n} → (A : Ty {n} Γ) → (σ : Subst Δ Γ) → Tm {n} Δ

data Subst where
  ids : ∀ {Γ} → Subst Γ Γ
  conss : ∀ {Γ Δ n} (σ : Subst Δ Γ) {A : Ty {n} Γ} → Tm {n} Δ  → Subst Δ (A :: Γ)

subRef = {!!}

subConcat σ τ = {!!}

subTm σ (Var r) = subRef σ r
subTm σ (Coh A τ) = Coh A (subConcat σ τ)

subTy σ ★ = ★
subTy σ (t ⇒ u) = subTm σ t ⇒ subTm σ u

RefTy : {Δ : List Pd} {n : ℕ} → Ref n Δ → Ty {n} Δ
RefTy {n = O} r = ★
RefTy {n = S n} r = Var (dom r) ⇒ Var (cod r)

data Of {n : ℕ} {Δ : List Pd} : Tm {n} Δ → Ty {n} Δ → Set where
  OfVar : (r : Ref n Δ) → Of (Var r) (RefTy r)

data WfTy {Δ : List Pd} : {n : ℕ} → Ty {n} Δ → Set where
  WfTy★ : WfTy {n = 0} ★
  WfTy⇒# : ∀ {n} → {C D : Ty {n} Δ} {A B : Tm Δ} → Of A C → Of B D → C == D → WfTy (A ⇒ B)

OfX : {Δ : List Pd} {n : ℕ} (r : Ref (S n) Δ) → RefTy (dom r) == RefTy (cod r)
OfX {n = O} r = idp
OfX {n = S n} r = ap2 (λ x y → Var x ⇒ Var y) (domLemma r) (codLemma r)

RefWf : {Δ : List Pd} {n : ℕ} (r : Ref n Δ) → WfTy (RefTy r)
RefWf {n = O} r = WfTy★
RefWf {n = S n} r = WfTy⇒# (OfVar (dom r)) (OfVar (cod r)) (OfX r)

OfWf : ∀ {n} → {Δ : List Pd} {M : Tm {n} Δ} {A : Ty Δ} → Of M A → WfTy A
OfWf (OfVar r) = RefWf r
