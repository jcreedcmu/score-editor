{-# OPTIONS --without-K --rewriting #-}

module FinsterMimram2 where
open import HoTT
open import FinsterMimramBase


data Ty : (n : ℕ) (Δ : List Pd) → Set
data Tm : (n : ℕ) (Δ : List Pd) → Ty n Δ → Set
RefTy : {n : ℕ} {Δ : List Pd} → Ref n Δ → Ty n Δ
-- f= : ∀ {n Δ} {τ υ : Ty n Δ} → (t : Tm n Δ τ) (u : Tm n Δ υ) → τ == υ → Ty (S n) Δ
sameTy : {Δ : List Pd} {n : ℕ} (r : Ref (S n) Δ) → RefTy (dom r) == RefTy (cod r)
apRtl : {n : ℕ} {Δ : Pd} {Δs : List Pd} → Ty n Δs → Ty n (Δ :: Δs)

data Tm where
  Var : ∀ {n Δ} (r : Ref n Δ) → Tm n Δ (RefTy r)



data Ty where
  ★ : ∀ {n Δ} → Ty n Δ
  f= : ∀ {n Δ} {τ υ : Ty n Δ} → (t : Tm n Δ τ) (u : Tm n Δ υ) → τ == υ → Ty (S n) Δ
-- {τ : Ty n Δ} → (t u : Tm n Δ τ) → Ty (S n) Δ
-- f= t u idp = t ⇒ u

dbd : {Δ : List Pd} {n : ℕ} (r : Ref (S (S n)) Δ) →
      f= (Var (dom (dom r))) (Var (cod (dom r))) (sameTy (dom r))
      == f= (Var (dom (cod r))) (Var (cod (cod r))) (sameTy (cod r))

RefTy {n = O} r = ★
RefTy {n = S n} {Δ} r = f= (Var (dom r)) (Var (cod r)) (sameTy r)

maybe : {n : ℕ} {Δ : Pd} {Δs : List Pd} {r s : Ref n Δs} → RefTy r == RefTy s → RefTy (rtl {Δ = Δ} r) == RefTy (rtl s)
maybe {O} q = idp
maybe {S n} q = {!!}

apRtl ★ = ★
apRtl (f= (Var r) (Var s) q) = f= (Var (rtl r)) (Var (rtl s)) (maybe q)

circle : {n : ℕ} {Δ : Pd} {Δs : List Pd} (r : Ref n Δs) → apRtl {Δ = Δ} (RefTy r) == RefTy (rtl r)
circle {O} r = idp
circle {S n} r = {!cod (rtl r) !}

foo : {n : ℕ} {Δ : Pd} {Δs : List Pd} (r : Ref (S n) Δs) → cod (rtl {Δ = Δ} r) == rtl (cod r)
foo = λ r → {!idp!}

sameTy {Δ} {O} r = idp
sameTy {Δ} {S n} r = dbd r

dbd {n = O} (rtl r) = {!dbd r!}
dbd {n = O} (rhd r) = idp
dbd {n = S n} (rtl r) = {!dbd r!}
dbd {n = S n} (rhd r) = {!dbd r!}
