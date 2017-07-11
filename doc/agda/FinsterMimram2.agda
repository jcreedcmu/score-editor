{-# OPTIONS --without-K --rewriting #-}

module FinsterMimram2 where
open import HoTT
open import FinsterMimramBase


data Ty : (n : ℕ) (Δ : List Pd) → Set
data Tm : (n : ℕ) (Δ : List Pd) → Ty n Δ → Set
RefTy : {n : ℕ} {Δ : List Pd} → Ref n Δ → Ty n Δ
-- f= : ∀ {n Δ} {τ υ : Ty n Δ} → (t : Tm n Δ τ) (u : Tm n Δ υ) → τ == υ → Ty (S n) Δ
sameTy : {Δ : List Pd} {n : ℕ} (r : Ref (S n) Δ) → RefTy (dom r) == RefTy (cod r)

data Tm where
  Var : ∀ {n Δ} (r : Ref n Δ) → Tm n Δ (RefTy r)

data Ty where
  ★ : ∀ {n Δ} → Ty n Δ
  f= : ∀ {n Δ} {τ υ : Ty n Δ} → (t : Tm n Δ τ) (u : Tm n Δ υ) → τ == υ → Ty (S n) Δ
-- {τ : Ty n Δ} → (t u : Tm n Δ τ) → Ty (S n) Δ
-- f= t u idp = t ⇒ u

ggdbd : {Δ : List Pd} {n : ℕ} (r1 r2 : Ref n Δ) →
       (p q : RefTy r1 == RefTy r2) (meta : p == q) →
       f= (Var r1) (Var r2) p == f= (Var r1) (Var r2) q
ggdbd r1 r2 p .p idp = idp

gdbd : {Δ : List Pd} {n : ℕ} (r1 r2 r3 r4 : Ref n Δ) →
       (pp : r1 == r3) (qq : r2 == r4)
       (p : RefTy r1 == RefTy r2) (q : RefTy r3 == RefTy r4) →
       (meta : coe (ap2 (λ r1 r2 → RefTy r1 == RefTy r2) pp qq) p == q) →
       f= (Var r1) (Var r2) p == f= (Var r3) (Var r4) q
gdbd r1 r2 .r1 .r2 idp idp p q meta = ggdbd r1 r2 p q meta

dbd : {Δ : List Pd} {n : ℕ} (r : Ref (S (S n)) Δ) →
      f= (Var (dom (dom r))) (Var (cod (dom r))) (sameTy (dom r))
      == f= (Var (dom (cod r))) (Var (cod (cod r))) (sameTy (cod r))

RefTy {n = O} r = ★
RefTy {n = S n} {Δ} r = f= (Var (dom r)) (Var (cod r)) (sameTy r)


sameTy {Δ} {O} r = idp
sameTy {Δ} {S n} r = dbd r

hard : {Δ : List Pd} {n : ℕ} (r : Ref (S (S n)) Δ) →
     coe
     (ap2 (λ r1 r2 → RefTy r1 == RefTy r2) (domLemma r) (codLemma r))
     (sameTy (dom r))
     == sameTy (cod r)
hard = {!!}

dbd {Δ} {n} r = gdbd {Δ} {n} (dom (dom r)) (cod (dom r)) (dom (cod r)) (cod (cod r)) (domLemma r) (codLemma r) (sameTy (dom r)) (sameTy (cod r)) (hard r)
