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
data Tm : (Δ : List Pd) → Ty Δ → Set
Vtype : {Δ : List Pd} (n : ℕ) (r : Ref n Δ) → Ty Δ
VtypeLemma : {Δ : List Pd} (n : ℕ) (r : Ref (S n) Δ) → Vtype n (dom r) == Vtype n (cod r)
_⇒_#_ : ∀ {Δ C D} → Tm Δ C → Tm Δ D → C == D → Ty Δ


data Ty where
  ★ : ∀ {Δ} → Ty Δ
  _⇒_ : ∀ {Δ C} → Tm Δ C → Tm Δ C → Ty Δ

t ⇒ u # idp = t ⇒ u

⇒=0 : ∀ {Δ C D} → {r1 r1' : Tm Δ C} {r2 r2' : Tm Δ D} {q q' : C == D} → r1 == r1' → r2 == r2' → q == q' → (r1 ⇒ r2 # q) == (r1' ⇒ r2' # q')
⇒=0 idp idp idp = idp

data Tm where
  Varn : ∀ {Δ n} → (r : Ref n Δ) → Tm Δ (Vtype n r)

2pathover : {A B : Set} → (C : A → B → Set) → {a1 a2 : A} {b1 b2 : B} → a1 == a2 → b1 == b2 → (C a1 b1) → (C a2 b2) → Set
2pathover {A} {B} C idp idp ℂ1 ℂ2 = ℂ1 == ℂ2

splat : ∀ {Δ n r1 r2 r1' r2'}
   → (t1 : Tm Δ (Vtype n r1)) (t1' : Tm Δ (Vtype n r1')) → (q1 : r1 == r1') → t1 == t1' [ (λ z → Tm Δ (Vtype n z)) ↓ q1 ]
   → (t2 : Tm Δ (Vtype n r2)) (t2' : Tm Δ (Vtype n r2')) → (q2 : r2 == r2') → t2 == t2' [ (λ z → Tm Δ (Vtype n z)) ↓ q2 ]
   → (w : Vtype n r1 == Vtype n r2)
   → (w' : Vtype n r1' == Vtype n r2')
   → (2pathover (λ z1 z2 → Vtype n z1 == Vtype n z2) q1 q2 w w')
   → (t1 ⇒ t2 # w) == (t1' ⇒ t2' # w')
splat t1 .t1 idp idp t2 .t2 idp idp w .w idp = idp

Vtype 0 r = ★
Vtype (S n) r = Varn (dom r) ⇒ Varn (cod r) # VtypeLemma n r

VtypeLemma O r = idp
VtypeLemma (S n) r = splat
  (Varn (dom (dom r))) (Varn (dom (cod r))) (domLemma r) (apd Varn (domLemma r))
  (Varn (cod (dom r))) (Varn (cod (cod r))) (codLemma r) (apd Varn (codLemma r))
  (VtypeLemma n (dom r)) (VtypeLemma n (cod r)) {!!}

-- {!splat (Varn (dom (dom r))) (Varn (dom (cod r))) (domLemma r) (apd Varn (domLemma r))!}



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
