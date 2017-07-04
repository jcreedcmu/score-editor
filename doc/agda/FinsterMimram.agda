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

-- OfWfEq : ∀ {n Δ A B C D} → (x : Of {n} {Δ} A C) (y : Of B D) → (q : C == D) → OfWf x == OfWf y [ WfTy ↓ q ]
-- OfWfEq {O} (OfVar r) (OfVar s) idp = idp
-- OfWfEq {S n} (OfVar r) (OfVar s) q = lem (OfX r) (OfX s)

Porefl' : {A : Set} {B : A → Set} {a a' : A} {u : B a} {u' : B a'} → ((a : A) (x y : B a) → x == y) →  (q : a == a') → u == u' [ B ↓ q ]
Porefl' {a = a} {u = u} {u'} contr idp = contr a u u'

OfEq0 : ∀ {n Δ} → (A : Tm0 {n} Δ) (B1 B2 : Ty0 Δ) (of1 : Of A B1) (of2 : Of A B2) → B1 == B2
OfEq0 {O} .(Var0 r) .★0 .★0 (OfVar r) (OfVar .r) = idp
OfEq0 {S n} .(Var0 r) .(Var0 (dom r) ⇒0 Var0 (cod r)) .(Var0 (dom r) ⇒0 Var0 (cod r)) (OfVar r) (OfVar .r) = idp

OfEq2 : ∀ {n Δ} → (A : Tm0 {n} Δ) (B1 B2 : Ty0 Δ) (of1 : Of A B1) (of2 : Of A B2) → of1 == of2 [ Of A ↓ OfEq0 A B1 B2 of1 of2 ]
OfEq2 {O} .(Var0 r) .★0 .★0 (OfVar r) (OfVar .r) = idp
OfEq2 {S n} .(Var0 r) .(Var0 (dom r) ⇒0 Var0 (cod r)) .(Var0 (dom r) ⇒0 Var0 (cod r)) (OfVar r) (OfVar .r) = idp

WfTy⇒Σ : ∀ {n Δ} → {A B : Tm0 Δ} → Σ (Ty0 {n} Δ) (λ C → Of A C × Of B C) → WfTy (A ⇒0 B)
WfTy⇒Σ (C , (ofA , ofB)) = WfTy⇒ ofA ofB


OfEqΣ : ∀ {n Δ} → (t : Tm0 {n} Δ) (of1 of2 : Σ (Ty0 Δ) (Of t)) → of1 == of2
OfEqΣ {O} .(Var0 r) (.★0 , OfVar r) (.★0 , OfVar .r) = idp
OfEqΣ {S n} .(Var0 r) (.(Var0 (dom r) ⇒0 Var0 (cod r)) , OfVar r) (.(Var0 (dom r) ⇒0 Var0 (cod r)) , OfVar .r) = idp

OfEq2b : ∀ {n Δ} → (A : Tm0 {n} Δ) (B : Ty0 Δ) (of1 : Of A B) (of2 : Of A B) → of1 == of2
OfEq2b {n} {Δ} A B of1 of2 = {!!} where


WfLem3 : ∀ {n Δ A B} → (p1 p2 : Σ (Ty0 {n} Δ) (λ C → Of A C × Of B C)) → p1 == p2
WfLem3 {O} (.★0 , OfVar r₁ , OfVar r) (.★0 , OfVar .r₁ , OfVar .r) = idp
WfLem3 {S n} (.(Var0 (dom r) ⇒0 Var0 (cod r)) , OfVar r , ofB1) (.(Var0 (dom r) ⇒0 Var0 (cod r)) , OfVar .r , ofB2) =
  ap (λ z → (Var0 (dom r) ⇒0 Var0 (cod r)) , OfVar r , z) (OfEq2b _ (Var0 (dom r) ⇒0 Var0 (cod r)) ofB1 ofB2)
--  ap (λ z → (Var0 (dom r) ⇒0 Var0 (cod r)) , OfVar r , z) (OfEq2a _ (Var0 (dom r) ⇒0 Var0 (cod r)) (Var0 (dom r) ⇒0 Var0 (cod r)) ofB1 ofB2 idp)

{- WfLem3 (C1 , ofA1 , ofB1) (C2 , ofA2 , ofB2) = foo where
  foo : mash (C1 , ofA1) (C1 , ofB1) idp == mash (C2 , ofA2) (C2 , ofB2) idp
  foo = mashLem (C1 , ofA1) (C1 , ofB1) idp (C2 , ofA2) (C2 , ofB2) idp -}

WfEq2 : ∀ {n Δ C} → (wf1 wf2 : WfTy {Δ} {n} C) → wf1 == wf2
WfEq2 {O} {Δ} WfTy★ WfTy★ = idp
WfEq2 {S n} {Δ} (WfTy⇒ {C = C1} {A} {B} a1 b1) (WfTy⇒ {C = C2} a2 b2) = ap WfTy⇒Σ (WfLem3 (C1 , (a1 , b1)) (C2 , (a2 , b2)))

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
ExtractTy (WfTy⇒ x y) = ExtractTm x (OfWf x) idp ⇒ ExtractTm y (OfWf x) (WfEq2 (OfWf y) (OfWf x))

{-


OfDecomp : ∀ {n Δ t A} → Of {n} {Δ} t A → Ref n Δ
OfDecomp (OfVar r) = r

OfDecompℓ : ∀ {n Δ t1 t2 A1 A2} (of1 : Of {n} {Δ} t1 A1) (of2 : Of t2 A2) → t1 == t2 → OfDecomp of1 == OfDecomp of2
OfDecompℓ (OfVar r) (OfVar .r) idp = idp

OfWhat : ∀ {n Δ t A} (of1 of2 : Of {n} {Δ} t A) (q : OfDecomp of1 == OfDecomp of2) → OfVar (OfDecomp of1) == OfVar (OfDecomp of2) [ (λ z → Of (Var0 z) (RefTy z)) ↓ q ]
OfWhat (OfVar r) of2 q = {!!}


Var0η : ∀ {n Δ t A} (of : Of {n} {Δ} t A) → t == Var0 (OfDecomp of)
Var0η (OfVar r) = idp

RefTyη : ∀ {n Δ t A} (of : Of {n} {Δ} t A) → A == RefTy (OfDecomp of)
RefTyη (OfVar r) = idp

Ofη : ∀ {n Δ t A} → Of {n} {Δ} t A → Set
Ofη of = OfVar (OfDecomp of) == coe (ap2 Of (Var0η of) (RefTyη of)) of

-}
