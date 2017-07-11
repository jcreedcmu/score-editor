{-# OPTIONS --without-K --rewriting #-}

module FinsterMimramBase where
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

postulate
  _~>_ : ∀ {n} {A : Set n} → A → A → Set

data Subst : (Δ : List Pd) (A : Set) → Set₁
getSubHead : {Δ : List Pd} {A : Set} → Subst Δ A → A


data Subst where
  snil :  {A : Set} (a : A) → Subst nil A
  scons :  {Δhd Δtl : List Pd} {A : Set} {a : A} (σtl : Subst Δtl A) (σhd : Subst Δhd (a ~> getSubHead σtl)) → Subst (pc Δhd :: Δtl) A

getSubHead (snil a) = a
getSubHead (scons {a = a} σtl σh) = a
