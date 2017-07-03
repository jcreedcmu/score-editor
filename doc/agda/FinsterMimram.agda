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

unpc : Pd → List Pd
unpc (pc x) = x

data Ty : List Pd → Set
data Tm : List Pd → Set

data Ty where
  ★ : ∀ {Δ} → Ty Δ
  _⇒_ : ∀ {Δ} → Tm Δ → Tm Δ → Ty Δ

data Tm where
  Var : ∀ {Δ n} → (r : Ref n Δ) → Tm Δ

RefTy : {Δ : List Pd} {n : ℕ} → Ref n Δ → Ty Δ
RefTy {n = O} r = ★
RefTy {n = S n} r = Var (dom r) ⇒ Var (cod r)

data Of {Δ : List Pd} : Tm Δ → Ty Δ → Set where
  OfVar : {n : ℕ} (r : Ref n Δ) → Of (Var r) (RefTy r)

data WfTy {Δ : List Pd} : Ty Δ → Set where
  WfTy★ : WfTy ★
  WfTy⇒ : {C : Ty Δ} {A B : Tm Δ} → Of A C → Of B C → WfTy (A ⇒ B)

WfTy⇒# : ∀ {Δ} → {C D : Ty Δ} {A B : Tm Δ} → Of A C → Of B D → C == D → WfTy (A ⇒ B)
WfTy⇒#  ofA ofB idp = WfTy⇒ ofA ofB

OfX : {Δ : List Pd} {n : ℕ} (r : Ref (S n) Δ) → RefTy (dom r) == RefTy (cod r)
OfX {n = O} r = idp
OfX {n = S n} r = ap2 (λ x y → Var x ⇒ Var y) (domLemma r) (codLemma r)

RefWf : {Δ : List Pd} {n : ℕ} (r : Ref n Δ) → WfTy (RefTy r)
RefWf {n = O} r = WfTy★
RefWf {n = S n} r = WfTy⇒# (OfVar (dom r)) (OfVar (cod r)) (OfX r)

OfWf : {Δ : List Pd} {M : Tm Δ} {A : Ty Δ} → Of M A → WfTy A
OfWf (OfVar r) = RefWf r
