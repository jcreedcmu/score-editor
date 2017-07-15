{-# OPTIONS --without-K --rewriting #-}

module DeBruijn where

open import HoTT hiding (ℕ ; O ; S ; _∈_ ; All ; Any ; Fin)

data ℕ : Set where
  O : ℕ
  S : (n : ℕ) → ℕ

data Ctx : Set
data Ty : Ctx → Set
data Tm : (Γ : Ctx) → Ty Γ → Set
data Ctx where
  cnil : Ctx
  _#_ : (Γ : Ctx) → Ty Γ → Ctx
shiftTy : ∀ {Γ} {X : Ty Γ} → Ty Γ → Ty (Γ # X)
data Reshift : Ctx → Ctx → Set -- reified shift operator
data ∋ : (Γ : Ctx) → Ty Γ → Set
applyTy : ∀ {Γ Δ} → Reshift Δ Γ → Ty Γ → Ty Δ
applyTm : ∀ {Γ Δ A} (ρ : Reshift Δ Γ) → Tm Γ A → Tm Δ (applyTy ρ A)
applyVar : ∀ {Γ Δ A} (ρ : Reshift Δ Γ) → A ∈ Γ → (applyTy ρ A) ∈ Δ

data Ty where
  o : {Γ : Ctx} → Ty Γ
  _⇒_ : {Γ : Ctx} → Ty Γ → Ty Γ → Ty Γ

data ∋ where
  f0 : ∀ {Γ A} → ∋ (Γ # A) (shiftTy A)
  fS : ∀ {Γ B A} → ∋ Γ A → ∋ (Γ # B) (shiftTy A)

syntax ∋ Γ A = A ∈ Γ

data Tm where
  Var : ∀ {Γ A} → A ∈ Γ → Tm Γ A
  App : ∀ {Γ A B} → Tm Γ (A ⇒ B) → Tm Γ A → Tm Γ B
  Lam : ∀ {Γ A B} → Tm (Γ # A) (shiftTy B) → Tm Γ (A ⇒ B)

data Reshift where
  rid : ∀ {Γ} → Reshift Γ Γ
  rshift : ∀ {Γ Δ A} → Reshift Δ Γ → Reshift (Δ # A) Γ
  rdelay : ∀ {Γ Δ A} (ρ : Reshift Δ Γ) → Reshift (Δ # (applyTy ρ A)) (Γ # A)

shiftTy A = applyTy (rshift rid) A

applyTy ρ o = o
applyTy ρ (t ⇒ u) = applyTy ρ t ⇒ applyTy ρ u

⇒= : ∀ {Γ} {t1 t2 u1 u2 : Ty Γ} → (t1 == t2) → (u1 == u2) → (t1 ⇒ u1) == (t2 ⇒ u2)
⇒= idp idp = idp

appThm1 : {Γ Δ : Ctx} {ρ  : Reshift Δ Γ} ({A} {B} : Ty Γ) →  applyTy (rdelay {A = A} ρ) (shiftTy B) == shiftTy (applyTy ρ B)
appThm1 {B = o} = idp
appThm1 {B = B1 ⇒ B2} = ⇒= (appThm1 {B = B1}) (appThm1 {B = B2})

appThm2 : {Γ : Ctx} {A : Ty Γ} → A == applyTy rid A
appThm2 {A = o} = idp
appThm2 {A = A1 ⇒ A2} = ⇒= (appThm2 {A = A1}) (appThm2 {A = A2})

appThm3 : {Γ Δ : Ctx} {ρ : Reshift Δ Γ} {A : Ty Γ} {X : Ty Δ} → shiftTy {X = X} (applyTy ρ A) == applyTy (rshift ρ) A
appThm3 {A = o} = idp
appThm3 {A = A1 ⇒ A3} = ⇒= (appThm3 {A = A1}) (appThm3 {A = A3})

applyTm ρ (Var x) = Var (applyVar ρ x)
applyTm ρ (App M N) = App (applyTm ρ M) (applyTm ρ N)
applyTm {Δ = Δ} ρ (Lam {A = A} {B} M) = Lam (transport (Tm (Δ # applyTy ρ A)) appThm1 (applyTm (rdelay ρ) M))

applyVar rid n = transport (∋ _) appThm2 n
applyVar (rshift ρ) n = transport (∋ _) appThm3 (fS (applyVar ρ n))
applyVar (rdelay ρ) f0 = transport (∋ _) (! appThm1) f0
applyVar (rdelay ρ) (fS n) = transport (∋ _) (! appThm1) (fS (applyVar ρ n))

{-

data Subst : Ctx → Ctx → Set where
  snil : ∀ {Γ} → Subst Γ cnil
  scons : ∀ {Γ Δ A} → Subst Γ Δ → Tm Γ A → Subst Γ (ccons Δ A)

substvar : ∀ {Γ Δ A} → Subst Δ Γ → A ∈ Γ → Tm Δ A
substvar (scons σ x) f0 = x
substvar (scons σ x) (fS ι) = substvar σ ι

shift : ∀ {Γ Δ A} → Subst Δ Γ → Subst (ccons Δ A) Γ
shift snil = snil
shift (scons σ t) = scons (shift σ) (apply (rshift rid) t)

subst : ∀ {Γ Δ A} → Subst Δ Γ → Tm Γ A → Tm Δ A
subst σ (Var x) = substvar σ x
subst σ (App M N) = App (subst σ M) (subst σ N)
subst σ (Lam M) = Lam (subst (scons (shift σ) (Var f0)) M)

idσ : (Γ : Ctx) → Subst Γ Γ
idσ cnil = snil
idσ (ccons Γ A) = scons (shift (idσ Γ)) (Var f0)

1subst : ∀ {Γ A B} → Tm Γ B → Tm (ccons Γ B) A →  Tm Γ A
1subst {Γ} {A} {B} t u = subst (scons (idσ Γ) t) u where
-}
