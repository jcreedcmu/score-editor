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
  WfTy⇒# : ∀ {n} → {C D : Ty0 {n} Δ} {A B : Tm0 Δ} → Of A C → Of B D → C == D → WfTy (A ⇒0 B)

WfTy⇒ : ∀ {Δ n} → {C : Ty0 {n} Δ} {A B : Tm0 Δ} → Of A C → Of B C → WfTy (A ⇒0 B)
WfTy⇒ ofA ofB = WfTy⇒# ofA ofB idp

OfX : {Δ : List Pd} {n : ℕ} (r : Ref (S n) Δ) → RefTy (dom r) == RefTy (cod r)
OfX {n = O} r = idp
OfX {n = S n} r = ap2 (λ x y → Var0 x ⇒0 Var0 y) (domLemma r) (codLemma r)

RefWf : {Δ : List Pd} {n : ℕ} (r : Ref n Δ) → WfTy (RefTy r)
RefWf {n = O} r = WfTy★
RefWf {n = S n} r = WfTy⇒# (OfVar (dom r)) (OfVar (cod r)) (OfX r)

OfWf : ∀ {n} → {Δ : List Pd} {M : Tm0 {n} Δ} {A : Ty0 Δ} → Of M A → WfTy A
OfWf (OfVar r) = RefWf r

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

REq : (n : ℕ) → ∀ {Δ} → (r1 r2 : Ref n Δ) (rta rtb : Var0 r1 == Var0 r2) → rta == rtb
REq .0 r0 r0 idp idp = idp
REq .0 r0 (rtl r2) () rtb
REq .0 (rtl r1) r0 rta ()
REq n (rtl r1) (rtl r2) rta rtb = {!!}
REq .(S _) (rtl r1) (rhd r2) rta rtb = {!!}
REq .(S _) (rhd r1) (rtl r2) rta rtb = {!!}
REq .(S _) (rhd r1) (rhd r2) rta rtb = {!!}

TmEq : ∀ {n Δ} → (t1 t2 : Tm0 {n} Δ) (rta rtb : t1 == t2) → rta == rtb
TmEq (Var0 r1) (Var0 r2) rta rtb = REq _ _ _ rta rtb

TyEqDecomp : ∀ {n Δ} → {a b c d : Tm0 {n} Δ} → (a ⇒0 b) == (c ⇒0 d) → (a == c) × (b == d)
TyEqDecomp idp = idp , idp

TyEqRecomp : ∀ {n Δ} → {a b c d : Tm0 {n} Δ} →  (a == c) × (b == d) → (a ⇒0 b) == (c ⇒0 d)
TyEqRecomp (idp , idp) = idp

TyEqInv : ∀ {n Δ} → {a b c d : Tm0 {n} Δ} (p : (a ⇒0 b) == (c ⇒0 d)) → TyEqRecomp (TyEqDecomp p) == p
TyEqInv idp = idp

TyEqDecompInj : ∀ {n Δ} → {a b c d : Tm0 {n} Δ} (p q : (a ⇒0 b) == (c ⇒0 d)) → TyEqDecomp p == TyEqDecomp q → p == q
TyEqDecompInj p q s = ! (TyEqInv p) ∙ ap TyEqRecomp s ∙ TyEqInv q

TtEq : ∀ {n Δ} → (t1 t2 : Ty0 {n} Δ) (rta rtb : t1 == t2) → rta == rtb
TtEq {n} ★0 ★0 idp idp = idp
TtEq {.(S _)} ★0 (x ⇒0 x₁) () rtb
TtEq {.(S _)} (x ⇒0 x₁) ★0 rta ()
TtEq {.(S _)} (a ⇒0 b) (c ⇒0 d) rta rtb = TyEqDecompInj rta rtb (pair×= z1 z2)  where
  decompa : (a == c) × (b == d)
  decompa = TyEqDecomp rta
  decompb : (a == c) × (b == d)
  decompb = TyEqDecomp rtb
  z1 : fst decompa == fst decompb
  z1 = TmEq a c (fst decompa) (fst decompb)
  z2 : snd decompa == snd decompb
  z2 = TmEq b d (snd decompa) (snd decompb)

RefWfLem2 : ∀ {Δ n} → (A B : Ty0 {n} Δ) (p : A == B) (wfA : WfTy A) (wfB : WfTy B) → wfA == wfB [ WfTy ↓ p ]
RefWfLem2 .★0 .★0 idp WfTy★ WfTy★ = idp
RefWfLem2 .(Var0 r1 ⇒0 Var0 r2) .(Var0 r1 ⇒0 Var0 r2) idp (WfTy⇒# (OfVar .r1) (OfVar .r2) rt1) (WfTy⇒# (OfVar r1) (OfVar r2) rt2) =
  ap (WfTy⇒# (OfVar r1) (OfVar r2)) (TtEq (RefTy r1) (RefTy r2) rt1 rt2)

RefWfLem : ∀ {Δ n} → (r1 r2 : Ref n Δ) (p : RefTy r1 == RefTy r2) → RefWf r1 == RefWf r2 [ WfTy ↓ p ]
RefWfLem r1 r2 p = RefWfLem2 (RefTy r1) (RefTy r2) p (RefWf r1) (RefWf r2)

OfLem : ∀ {Δ n A B C D} → (oa : Of {n} {Δ} A C) (ob : Of B D) (p : C == D) → OfWf oa == OfWf ob [ WfTy ↓ p ]
OfLem {n = n} (OfVar r1) (OfVar r2) p = RefWfLem r1 r2 p

ExtractTm (OfVar r) wf idp = Var r
ExtractTy WfTy★ = ★
ExtractTy (WfTy⇒# x y idp) = ExtractTm x (OfWf x) idp ⇒ ExtractTm y (OfWf x) (OfLem y x idp)
