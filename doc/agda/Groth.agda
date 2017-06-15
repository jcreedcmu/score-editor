{-# OPTIONS --without-K --rewriting #-}

open import HoTT hiding (Bool ; true ; false ; _$_ ; Path)

{- quick little proof of a grothendieck-like construction -}

module Groth where

flem : (A B : Set) (p : B → A) → Σ A (λ a → Σ B (λ b → p b == a)) ≃ B
flem A B p = equiv into out (λ b → idp) zag where
  into : Σ A (λ a → Σ B (λ b → p b == a)) → B
  into (_ , b , idp) = b
  out : B → Σ A (λ a → Σ B (λ b → p b == a))
  out b = p b , b , idp
  zag : (a : Σ A (λ a₁ → Σ B (λ b → p b == a₁))) → out (into a) == a
  zag (_ , b , idp) = idp

plem : {A : Set} (p : A → Set) (a : A) → Σ (Σ A p) (λ b → fst b == a) ≃ p a
plem {A} p a = equiv into out zig zag where
  into : Σ (Σ A p) (λ b → fst b == a) → p a
  into ((_ , pa) , idp) = pa
  out : p a → Σ (Σ A p) (λ b → fst b == a)
  out π = (a , π) , idp
  zig = λ _ → idp
  zag : (z : Σ (Σ A p) (λ b → fst b == a)) → out (into z) == z
  zag ((_ , pa) , idp) = idp

po2trans : {A : Set} {B : A → Set} {x y : A} {p : x == y} {u : B x} {v : B y}
  → u == v [ B ↓ p ] → coe (ap B p) u == v
po2trans {p = idp} po = po

trans2po : ∀ {i j} {A : Set i} {B : A → Set j} {x y : A} {p : x == y} {u : B x} {v : B y}
  → coe (ap B p) u == v → u == v [ B ↓ p ]
trans2po {p = idp} po = po

apOnDomain : {A B1 B2 : Set} (q : B1 == B2) (f : B1 → A) → coe (ap (λ B → B → A) q) f == (λ b2 → f (coe! q b2))
apOnDomain idp f = λ= (λ _ → idp)

apOnDomainUa : {A B1 B2 : Set} {q : B1 ≃ B2} {f : B1 → A} → coe (ap (λ B → B → A) (ua q)) f == (λ b2 → f (<– q b2))
apOnDomainUa {A} {B1} {B2} {q} {f} = apOnDomain (ua q) f ∙ (λ= (λ b2 → ap f (coe!-β q b2)))

groth : (A B : Set) → (A → Set) ≃ Σ Set (λ B → B → A)
groth A B = equiv into out zig zag where
  into : (A → Set) → Σ Set (λ B → B → A)
  into fib = (Σ A fib) , fst
  out : Σ Set (λ B → B → A) → A → Set
  out (B , p) = λ a → Σ B (λ b → p b == a)
  zig : (b : Σ Set (λ B → B → A)) → into (out b) == b
  zig (B , p) = pair= (ua (flem A B p)) (trans2po apOnDomainUa)
  zag2 : (p : A → Set) (a : A) → Σ (Σ A p) (λ b → fst b == a) == p a
  zag2 p a = ua (plem p a)
  zag : (p : A → Set) → out (into p) == p
  zag p =  λ= (zag2 p)
