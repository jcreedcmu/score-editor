{-# OPTIONS --without-K --rewriting #-}

module DeBruijn where

open import HoTT hiding (ℕ ; O ; S ; _∈_ ; All ; Any ; Fin)

data ℕ : Set where
  O : ℕ
  S : (n : ℕ) → ℕ

data Ty : Set where
  o : Ty
  _⇒_ : Ty → Ty → Ty

data Ctx : Set where
  cnil : Ctx
  ccons : Ctx → Ty → Ctx

data _∈_ : Ty → Ctx → Set where
  f0 : ∀ {A Γ} → A ∈ (ccons Γ A)
  fS : ∀ {A B Γ} → A ∈ Γ → A ∈ (ccons Γ B)

data Tm : Ctx → Ty → Set where
  Var : ∀ {Γ A} → A ∈ Γ → Tm Γ A
  App : ∀ {Γ A B} → Tm Γ (A ⇒ B) → Tm Γ A → Tm Γ B
  Lam : ∀ {Γ A B} → Tm (ccons Γ A) B → Tm Γ (A ⇒ B)

data Reshift : Ctx → Ctx → Set where -- reified shift operator
  rid : ∀ {Γ} → Reshift Γ Γ
  rshift : ∀ {Γ Δ A} → Reshift Δ Γ → Reshift (ccons Δ A) Γ
  rdelay : ∀ {Γ Δ A} → Reshift Δ Γ → Reshift (ccons Δ A) (ccons Γ A)

applyvar : ∀ {Γ Δ A} → Reshift Δ Γ → A ∈ Γ → A ∈ Δ
applyvar rid n = n
applyvar (rshift ρ) n = fS (applyvar ρ n)
applyvar (rdelay ρ) f0 = f0
applyvar (rdelay ρ) (fS n) = fS (applyvar ρ n)

apply : ∀ {Γ Δ A} → Reshift Δ Γ → Tm Γ A →  Tm Δ A
apply ρ (Var x) = Var (applyvar ρ x)
apply ρ (App M N) = App (apply ρ M) (apply ρ N)
apply ρ (Lam M) = Lam (apply (rdelay ρ) M)

data Subst : Ctx → Ctx → Set where
  snil : ∀ {Γ} → Subst Γ cnil
  scons : ∀ {Γ Δ A} → Subst Γ Δ → Tm Γ A → Subst Γ (ccons Δ A)

substvar : ∀ {Γ Δ A} → Subst Δ Γ → A ∈ Γ → Tm Δ A
substvar (scons σ x) f0 = x
substvar (scons σ x) (fS ι) = substvar σ ι

shift : ∀ {Γ Δ A} → Subst Δ Γ → Subst (ccons Δ A) Γ
shift snil = snil
shift (scons σ t) = scons (shift σ) (apply (rshift rid) t)

subst : ∀ {Γ Δ A} → Subst Δ Γ → Tm Γ A →  Tm Δ A
subst σ (Var x) = substvar σ x
subst σ (App M N) = App (subst σ M) (subst σ N)
subst σ (Lam M) = Lam (subst (scons (shift σ) (Var f0)) M)
