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

data Ty0 : {n : ℕ} → List Pd → Set
data Tm0 : {n : ℕ} → List Pd → Set

data Ty0 where
  ★0 : ∀ {Δ n} → Ty0 {n} Δ
  _⇒0_ : ∀ {Δ n} → Tm0 {n} Δ → Tm0 {n} Δ → Ty0 {S n} Δ

data Tm0 where
  Var0 : ∀ {Δ n} → (r : Ref n Δ) → Tm0 {n} Δ

RefTy : {Δ : List Pd} {n : ℕ} → Ref n Δ → Ty0 {n} Δ
RefTy {n = O} r = ★0
RefTy {n = S n} r = Var0 (dom r) ⇒0 Var0 (cod r)

data Of {n : ℕ} {Δ : List Pd} : Tm0 {n} Δ → Ty0 {n} Δ → Set where
  OfVar : (r : Ref n Δ) → Of (Var0 r) (RefTy r)

data WfTy {Δ : List Pd} : {n : ℕ} → Ty0 {n} Δ → Set where
  WfTy★ : WfTy {n = 0} ★0
  WfTy⇒ : ∀ {n} → {C : Ty0 {n} Δ} {A B : Tm0 Δ} → Of A C → Of B C → WfTy (A ⇒0 B)

WfTy⇒# : ∀ {Δ n} → {C D : Ty0 {n} Δ} {A B : Tm0 Δ} → Of A C → Of B D → C == D → WfTy (A ⇒0 B)
WfTy⇒#  ofA ofB idp = WfTy⇒ ofA ofB

OfX : {Δ : List Pd} {n : ℕ} (r : Ref (S n) Δ) → RefTy (dom r) == RefTy (cod r)
OfX {n = O} r = idp
OfX {n = S n} r = ap2 (λ x y → Var0 x ⇒0 Var0 y) (domLemma r) (codLemma r)

RefWf : {Δ : List Pd} {n : ℕ} (r : Ref n Δ) → WfTy (RefTy r)
RefWf {n = O} r = WfTy★
RefWf {n = S n} r = WfTy⇒# (OfVar (dom r)) (OfVar (cod r)) (OfX r)

OfWf : ∀ {n} → {Δ : List Pd} {M : Tm0 {n} Δ} {A : Ty0 Δ} → Of M A → WfTy A
OfWf (OfVar r) = RefWf r

{-- lemmas --}

bd : ∀ {n Δ} → (r : Ref (S n) Δ) → Ref n Δ × Ref n Δ
bd r = dom r , cod r



Poconst : {A B : Set} {u v : B} {x y : A} (q : x == y) → u == v [ (λ _ → B) ↓ q ] → u == v
Poconst idp p = p

Poconst' : {A B : Set} {u v : B} {x y : A} (q : x == y) → u == v → u == v [ (λ _ → B) ↓ q ]
Poconst' idp idp = idp

OfXℓ : ∀ {n Δ} → (r s : Ref (S n) Δ) → (q : bd r == bd s) → OfX r == OfX s [ (λ δ → RefTy (fst δ) == RefTy (snd δ)) ↓ q ]
OfXℓ {O} r s q = Poconst' q idp
OfXℓ {S n} r s q = {!!}
lem2 : {n  : ℕ}
  {Δ : List Pd}
  (rd rc sd sc  : Ref n Δ)
  {q  : (Var0 rd ⇒0 Var0 rc) == (Var0 sd ⇒0 Var0 sc)}
  (μr : RefTy rd == RefTy rc)
  (μs : RefTy sd == RefTy sc)
      →
        (WfTy⇒# (OfVar rd) (OfVar rc) μr) ==
        (WfTy⇒# (OfVar sd) (OfVar sc) μs) [ WfTy ↓ q ]
lem2 μr μs = {!!}

lem : {n  : ℕ}
  {Δ : List Pd}
  {r s  : Ref (S n) Δ}
  {q  : (Var0 (dom r) ⇒0 Var0 (cod r)) == (Var0 (dom s) ⇒0 Var0 (cod s))}
  (μr : RefTy (dom r) == RefTy (cod r))
  (μs : RefTy (dom s) == RefTy (cod s))
      →
        (WfTy⇒# (OfVar (dom r)) (OfVar (cod r)) μr) ==
        (WfTy⇒# (OfVar (dom s)) (OfVar (cod s)) μs) [ WfTy ↓ q ]
lem {r = r} {s} μr μs = lem2 (dom r) (cod r) (dom s) (cod s) μr μs

OfWfEq : ∀ {n Δ A B C D} → (x : Of {n} {Δ} A C) (y : Of B D) → (q : C == D) → OfWf x == OfWf y [ WfTy ↓ q ]
OfWfEq {O} (OfVar r) (OfVar s) idp = idp
OfWfEq {S n} (OfVar r) (OfVar s) q = lem (OfX r) (OfX s)

{--- build up intrinsic terms now ---}

data Ty : {n : ℕ} → List Pd → Set
data Tm : {n : ℕ} → (Δ : List Pd) → Ty {n} Δ → Set
ExtractTy : {n : ℕ} {Δ : List Pd} {τ : Ty0 {n} Δ} → WfTy τ → Ty {n} Δ
ExtractTm : {n : ℕ} {Δ : List Pd} {τ : Ty0 {n} Δ} {t : Tm0 Δ} (of : Of t τ) (wf : WfTy τ) (z : OfWf of == wf) →  Tm Δ (ExtractTy wf)

data Ty where
  ★ : ∀ {Δ} → Ty {0} Δ
  _⇒_ : ∀ {Δ n C} → Tm {n} Δ C → Tm {n} Δ C → Ty {S n} Δ

_#_⇒_ : ∀ {Δ n C D} → C == D → Tm {n} Δ C → Tm {n} Δ D → Ty {S n} Δ
_#_⇒_ idp = _⇒_

data Tm where
  Var : ∀ {Δ n} → (r : Ref n Δ) → Tm Δ (ExtractTy (RefWf r))

ExtractTm (OfVar r) wf idp = Var r
ExtractTy WfTy★ = ★
ExtractTy (WfTy⇒ x y) = ExtractTm x (OfWf x) idp ⇒ ExtractTm y (OfWf x) (OfWfEq y x idp)
