{-# OPTIONS --without-K --rewriting #-}

module FinsterMimram2 where
open import HoTT
open import FinsterMimramBase

data Tm : (n : ℕ) (Δ : List Pd) → Set
data Tm where
  Var : ∀ {n Δ} (r : Ref n Δ) → Tm n Δ


data Ty : (n : ℕ) (Δ : List Pd) → Set
RefTy : {n : ℕ} {Δ : List Pd} → Ref n Δ → Ty n Δ
Of : {n : ℕ} {Δ : List Pd} → Tm n Δ → Ty n Δ → Set

sameTy : {Δ : List Pd} {n : ℕ} (r : Ref (S n) Δ) → RefTy (dom r) == RefTy (cod r)


VarOf : {n : ℕ} {Δ : List Pd} (r : Ref n Δ) → Of (Var r) (RefTy r)

data Ty where
  ★ : ∀ {n Δ} → Ty n Δ
  f= : ∀ {n Δ} {τ υ : Ty n Δ}{t u : Tm n Δ} (of1 : Of t τ) (of2 : Of u υ) → τ == υ → Ty (S n) Δ

Of (Var r) τ = τ == RefTy r
VarOf r = idp

-- can I show that Ty is a set?

ofeqover : {n : ℕ} {Δ : List Pd} {t1 t2 : Tm n Δ} {τ1 τ2 : Ty n Δ} (of1 : Of t1 τ1) (of3 : Of t2 τ2) (et : t1 == t2) (eτ : τ1 == τ2) → Set
ofeqover of1 of3 idp idp = of1 == of3

record bundle {n : ℕ} {Δ : List Pd} {t1 t2 u1 u2 : Tm n Δ} {τ1 τ2 : Ty n Δ} (of1 : Of t1 τ1) (of2 : Of u1 τ1) (of3 : Of t2 τ2) (of4 : Of u2 τ2) : Set where
  constructor MkBundle
  field
    et : t1 == t2
    eu : u1 == u2
    eτ : τ1 == τ2
    e13 : ofeqover of1 of3 et eτ
    e24 : ofeqover of2 of4 eu eτ

tyCov : ∀ {n Δ} →  Ty n Δ → Ty n Δ → Set
tyCov ★ ★ = ⊤
tyCov ★ (f= of1 of2 x) = ⊥
tyCov (f= of1 of2 x) ★ = ⊥
tyCov (f= of1 of2 idp) (f= of3 of4 idp) = bundle of1 of2 of3 of4

tmCov : ∀ {n Δ} →  Tm n Δ → Tm n Δ → Set
tmCov (Var r) (Var s) = r == s

refCov : ∀ {n Δ} → Ref n Δ → Ref n Δ → Set
refCov r0 r0 = ⊤
refCov r0 _ = ⊥
refCov (rtl r) (rtl s) = r == s
refCov (rtl r) _ = ⊥
refCov (rhd r) (rhd s) = r == s
refCov (rhd r) _ = ⊥

tyThm : ∀ {n Δ} (τ1 τ2 : Ty n Δ) → (τ1 == τ2) == (tyCov τ1 τ2)
tyThm τ1 τ2 = ua (equiv (tyEnc τ1 τ2) (tyDec τ1 τ2) (tyEncDec τ1 τ2) (tyDecEnc τ1 τ2)) where
  tyEnc : ∀ {n Δ} (τ1 τ2 : Ty n Δ) → τ1 == τ2 → tyCov τ1 τ2
  tyEnc ★ .★ idp = tt
  tyEnc (f= of1 of2 idp) .(f= of1 of2 idp) idp = MkBundle idp idp idp idp idp

  tyDec : ∀ {n Δ} (τ1 τ2 : Ty n Δ) → tyCov τ1 τ2 → τ1 == τ2
  tyDec ★ ★ tc = idp
  tyDec ★ (f= of1 of2 x) ()
  tyDec (f= of1 of2 x) ★ ()
  tyDec (f= of1 of2 idp) (f= .of1 .of2 idp) (MkBundle idp idp idp idp idp) = idp

  tyEncDec : ∀ {n Δ} (τ1 τ2 : Ty n Δ) (p : tyCov τ1 τ2) → tyEnc τ1 τ2 (tyDec τ1 τ2 p) == p
  tyEncDec ★ ★ unit = idp
  tyEncDec ★ (f= of1 of2 x) ()
  tyEncDec (f= of1 of2 x) ★ ()
  tyEncDec (f= of1 of2 idp) (f= .of1 .of2 idp) (MkBundle idp idp idp idp idp) = idp

  tyDecEnc : ∀ {n Δ} (τ1 τ2 : Ty n Δ) (p : τ1 == τ2) → tyDec τ1 τ2 (tyEnc τ1 τ2 p) == p
  tyDecEnc ★ .★ idp = idp
  tyDecEnc (f= of1 of2 idp) .(f= of1 of2 idp) idp = idp


allTypeEqsEq :  ∀ {n Δ} {τ1 τ2 : Ty n Δ} (p q : τ1 == τ2) → p == q
allTypeEqsEq = {!!}

RefTy {n = O} r = ★
RefTy {n = S n} {Δ} r = f= (VarOf (dom r)) (VarOf (cod r)) (sameTy r)


core :  ∀ {n Δ} {r1 r2 r3 r4 : Ref n Δ} → (r1 == r3) → (r2 == r4) → (p : RefTy r1 == RefTy r2) (q : RefTy r3 == RefTy r4)
  → f= (VarOf r1) (VarOf r2) p == f= (VarOf r3) (VarOf r4) q
core idp idp p q = ap (f= (VarOf _) (VarOf _)) (allTypeEqsEq p q)

sameTy {Δ} {O} r = idp
sameTy  {n = S n} (r) = core (domLemma r) (codLemma r) (sameTy (dom r)) (sameTy (cod r))


ap2const : ∀ {n} {K : Set n} {V1 V2 : Set} (k : K) {v1a v1b : V1} {v2a v2b : V2} (p : v1a == v1b) (q : v2a == v2b) →  (ap2 (λ _ _ → k) p q) == idp
ap2const k idp idp = idp
