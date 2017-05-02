open import Data.Nat
open import Data.Unit
open import Data.Empty
open import Data.Bool
open import Data.Sum
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

module Summable where

data Fin : (n : ℕ) → Set where
  fz : {n : ℕ} -> Fin n
  fs : {n : ℕ} -> Fin n → Fin (suc n)

record _≅_ (A B : Set) : Set where
  field
    f : A → B
    g : B → A
    p1 : (x : A) → g (f x) ≡ x
    p2 : (x : B) → f (g x) ≡ x

record isFin (A : Set) : Set where
  field
    n : ℕ
    pf : A ≅ Fin n

summer : Set → Set
summer A = (A → ℕ) → ℕ


fin-cond : {n : ℕ} → Fin (suc n) → Fin n ⊎ ⊤
fin-cond fz = inj₂ tt
fin-cond (fs ff) = inj₁ ff

fin-summer : (n : ℕ) → (Fin n → ℕ) → ℕ
fin-summer zero k = zero
fin-summer (suc n) k = k fz + fin-summer n (λ x → k (fs x))

index : {n : ℕ} → Fin n → ℕ
index fz = zero
index (fs f) = suc (index f)

≅-summer : (A B : Set) -> summer A → A ≅ B → summer B
≅-summer A B iss cong F = iss (λ a → F (_≅_.f cong a))

≅-sym : {A B : Set} -> A ≅ B → B ≅ A
≅-sym record { f = f ; g = g ; p1 = p1 ; p2 = p2 } =
  record { f = g ; g = f ; p1 = p2 ; p2 = p1 }

isfin-summer : (A : Set) -> isFin A → summer A
isfin-summer A record { n = n ; pf = pf } =
  ≅-summer (Fin n) A (fin-summer n) (≅-sym pf)
