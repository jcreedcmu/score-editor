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




-- example
-- x y z : ⋆ / f g h : x → y / α β : f → g / γ : g → h / θ : α → β / q : y → z
-- x(f(α(θ)β)g(γ)h)y(q)z
--  ( ( ( ) ) ( ) ) ( )
-- ((())())()
ex : Pd
ex = pc (pc (pc (pc nil :: nil) :: pc nil :: nil) :: pc nil :: nil)


data Name : ℕ → Set where
  x y z : Name 0
  f g h q : Name 1
  α β γ : Name 2
  θ : Name 3

thmn : {n : ℕ} → Ref n (unpc ex) → Name n
thmn r0 = x
thmn (rtl r0) = y
thmn (rtl (rtl r0)) = z
thmn (rtl (rhd r0)) = q
thmn (rhd r0) = f
thmn (rhd (rtl r0)) = g
thmn (rhd (rtl (rtl r0))) = h
thmn (rhd (rtl (rhd r0))) = γ
thmn (rhd (rhd r0)) = α
thmn (rhd (rhd (rtl r0))) = β
thmn (rhd (rhd (rhd r0))) = θ

sem : {n : ℕ} → Name n → Ref n (unpc ex)
sem x = r0
sem y = rtl r0
sem z = rtl (rtl r0)
sem q = rtl (rhd r0)
sem f = rhd r0
sem g = rhd (rtl r0)
sem h = rhd (rtl (rtl r0))
sem γ = rhd (rtl (rhd r0))
sem α = rhd (rhd r0)
sem β = rhd (rhd (rtl r0))
sem θ = rhd (rhd (rhd r0))


bd : ∀ {n} → Name (S n) → Name n × Name n
bd c = thmn (dom (sem c)) , thmn (cod (sem c))

checkθ : bd θ == α , β
checkθ = idp

checkα : bd α == f , g
checkα = idp

checkβ : bd β == f , g
checkβ = idp

checkγ : bd γ == g , h
checkγ = idp

checkf : bd f == x , y
checkf = idp

checkg : bd g == x , y
checkg = idp

checkh : bd h == x , y
checkh = idp

checkq : bd q == y , z
checkq = idp




{-
record Glob : Set₁ where
  constructor MkGlob
  field
    K : ℕ → Set
    dom cod : ∀ {n} → K (S n) → K n
    p1 : ∀ {n} → (k : K (S (S n))) → dom (cod k) == dom {n} (dom k)
    p2 : ∀ {n} → (k : K (S (S n))) → cod (cod k) == cod {n} (dom k)

record Glob2 : Set₁ where
  constructor MkGlob2
  field
    Bd : ℕ → Set
    C : {n : ℕ} → Bd n → Set
    p0 : ⊤ ≃ Bd 0
    pS : (n : ℕ) → Σ (Bd n) (λ δ → C δ × C δ) ≃ Bd (S n)

postulate
  Hole : {A : Set} → A

thm : Glob ≃ Glob2
thm = equiv into out zig zag where
  into : Glob → Glob2
  into G = MkGlob2 Bd C (ide ⊤) (λ n → ide _) where
    open Glob G
    Bd : ℕ → Set
    C : {n : ℕ} → Bd n → Set
    compat : {n : ℕ} → Bd n → K n → Set

    Bd O = ⊤
    Bd (S n) = Σ (Bd n) (λ δ → C δ × C δ)
    C {n} δ = Σ (K n) (compat δ)
    compat {O} δ k = ⊤
    compat {S n} δ k = (fst (fst (snd δ)) == dom k) × (fst (snd (snd δ)) == cod k)

  out : Glob2 → Glob
  out G2 = MkGlob K dom cod p1 p2 where
    open Glob2 G2
    K : ℕ → Set
    K n = Σ (Bd n) C
    dom : ∀ {n} → K (S n) → K n
    dom {n} k = fst (<– (pS n) (fst k)) , fst (snd (<– (pS n) (fst k)))
    cod : ∀ {n} → K (S n) → K n
    cod {n} k = fst (<– (pS n) (fst k)) , snd (snd (<– (pS n) (fst k)))
    p1 : ∀ {n} → (k : K (S (S n))) → dom (cod k) == dom {n} (dom k)
    p1 k = idp
    p2 : ∀ {n} → (k : K (S (S n))) → cod (cod k) == cod {n} (dom k)
    p2 k = idp
  zigBd : (G2 : Glob2) → Glob2.Bd (into (out G2)) == Glob2.Bd G2
  zigBd G2  = λ= f where
    open Glob2 G2
    f : (n : ℕ) → Glob2.Bd (into (out G2)) n == Bd n
    f O = ua p0
    f (S n) = {!Glob2.Bd (into (out G2)) (S n)!} ∙ ua (pS n)

  zig : (G2 : Glob2) → into (out G2) == G2
  zig G2  = {!!} where
    open Glob2 G2
  zag = {!!}
-}

{-
 Var0 : ∀ {Δ} → Ref 0 Δ → Tm Δ ★
  Var1 : ∀ {Δ} → (r : Ref 1 Δ) → Tm Δ (Var0 (dom r) ⇒ Var0 (cod r) # idp)
  Var2 : ∀ {Δ} → (r : Ref 2 Δ) → Tm Δ (Var1 (dom r) ⇒ Var1 (cod r) # ⇒=0 (ap Var0 (domLemma r)) (ap Var0 (codLemma r)) idp)
  Var3 : ∀ {Δ} → (r : Ref 3 Δ) → Tm Δ (Var2 (dom r) ⇒ Var2 (cod r) # {!⇒=0 (ap Var0 (domLemma (cod r))) (ap Var0 (codLemma (cod r))) idp!})
-}
