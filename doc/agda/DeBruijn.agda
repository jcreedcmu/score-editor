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
data ReshiftNi : Ctx → Ctx → Set -- reified shift operator, not the identity
data ∋ : (Γ : Ctx) → Ty Γ → Set
applyTy : ∀ {Γ Δ} → Reshift Δ Γ → Ty Γ → Ty Δ
applyTyNi : ∀ {Γ Δ} → ReshiftNi Δ Γ → Ty Γ → Ty Δ
applyTm : ∀ {Γ Δ A} (ρ : Reshift Δ Γ) → Tm Γ A → Tm Δ (applyTy ρ A)
applyTmNi : ∀ {Γ Δ A} (ρ : ReshiftNi Δ Γ) → Tm Γ A → Tm Δ (applyTyNi ρ A)
applyVar : ∀ {Γ Δ A} (ρ : Reshift Δ Γ) → A ∈ Γ → (applyTy ρ A) ∈ Δ
applyVarNi : ∀ {Γ Δ A} (ρ : ReshiftNi Δ Γ) → A ∈ Γ → (applyTyNi ρ A) ∈ Δ

data Ty where
  o : {Γ : Ctx} → Ty Γ
  _⇒_ : {Γ : Ctx} → Ty Γ → Ty Γ → Ty Γ
  pi : {Γ : Ctx} (A : Ty Γ) (B : Ty (Γ # A)) → Ty Γ

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
  rcomp : ∀ {Γ Δ Ω} → Reshift Γ Δ → Reshift Δ Ω → Reshift Γ Ω
  rni : ∀ {Δ Γ} → ReshiftNi Δ Γ → Reshift Δ Γ


data ReshiftNi where
  rshift : ∀ {Δ A} → ReshiftNi (Δ # A) Δ
  rdelay : ∀ {Γ Δ A} (ρ : ReshiftNi Δ Γ) → ReshiftNi (Δ # (applyTyNi ρ A)) (Γ # A)

shiftTy A = applyTy (rni rshift) A

applyTy rid t = t
applyTy (rni ρ) t = applyTyNi ρ t
applyTy (rcomp σ ρ) t = applyTy σ (applyTy ρ t)
applyTyNi ρ o = o
applyTyNi ρ (t ⇒ u) = applyTyNi ρ t ⇒ applyTyNi ρ u
applyTyNi ρ (pi A B) = pi (applyTyNi ρ A) (applyTyNi (rdelay ρ) B)

⇒= : ∀ {Γ} {t1 t2 u1 u2 : Ty Γ} → (t1 == t2) → (u1 == u2) → (t1 ⇒ u1) == (t2 ⇒ u2)
⇒= idp idp = idp

pi= : ∀ {Γ} {t1 t2 : Ty Γ} {u1 : Ty (Γ # t1)} {u2 : Ty (Γ # t2)} (p : t1 == t2) → (u1 == u2 [ (λ z → Ty (Γ # z)) ↓ p ]) → (pi t1 u1) == (pi t2 u2)
pi= idp idp = idp



appThm1Ni : {Γ Δ : Ctx} {ρ  : ReshiftNi Δ Γ} ({A} {B} : Ty Γ) →  applyTyNi (rdelay {A = A} ρ) (shiftTy B) == shiftTy (applyTyNi ρ B)
appThm1Ni {B = o} = idp
appThm1Ni {B = B1 ⇒ B2} = ⇒= (appThm1Ni {B = B1}) (appThm1Ni {B = B2})
appThm1Ni {B = pi A B0} = pi= (appThm1Ni {B = A}) {!!} -- pi= (appThm1Ni {B = A}) {!!}


applyTm rid t = t
applyTm (rni ρ) t = applyTmNi ρ t
applyTm (rcomp σ ρ) t = applyTm σ (applyTm ρ t)

applyTmNi ρ (Var x) = Var (applyVarNi ρ x)
applyTmNi ρ (App M N) = App (applyTmNi ρ M) (applyTmNi ρ N) -- App (applyTm ρ M) (applyTm ρ N)
applyTmNi {Γ} {Δ} ρ (Lam {A = A} {B} M) = Lam (transport (Tm (Δ # applyTyNi ρ A)) (appThm1Ni) (applyTmNi (rdelay ρ) M))
applyVar rid n = n
applyVar (rni ρ) n = applyVarNi ρ n
applyVar (rcomp σ ρ) n = applyVar σ (applyVar ρ n)
applyVarNi rshift n = fS n
applyVarNi (rdelay ρ) f0 = transport (∋ _) (! appThm1Ni) f0
applyVarNi (rdelay ρ) (fS n) = transport (∋ _) (! appThm1Ni) (fS (applyVarNi ρ n))


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
