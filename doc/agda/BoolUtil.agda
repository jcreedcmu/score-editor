{-# OPTIONS --experimental-irrelevance #-}

module BoolUtil where
open import Level
open import Data.Bool
open import Data.Product
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; cong; trans)
open import Data.Sum renaming ( _⊎_ to _⊕_ )

record _st_{a b} (A : Set a) (B : A → Set b) : Set (a ⊔ b) where
  constructor _,,_
  field
    Item : A
    .Pf : B Item -- proof irrelevance
open _st_ public

Bool= : Bool → Bool → Bool
Bool= true true = true
Bool= false false = true
Bool= _ _ = false

NonTriv : {B : Set} → (B → Bool) → Set
NonTriv {B} pred = Σ B (λ b → (pred b ≡ true))

Uniq : (B : Set) → (B → Bool) → Set
Uniq B pred = Σ B (λ b → (pred b ≡ true) × ((b' : B) → pred b' ≡ true → b ≡ b'))

None : (B : Set) → (B → Bool) → Set
None B pred = (b : B) → pred b ≡ false

Calm : (B : Set) (f g : B → Bool) → Set
Calm B f g = (Uniq B f × Uniq B g) ⊕ (None B f × None B f)

module Bool⊑ where
  _⊑_ : Bool → Bool → Bool
  false ⊑ true = true
  true ⊑ true = true
  _ ⊑ _ = false
open Bool⊑

module Func⊑ where
  _f⊑_ : {A : Set} → (A → Bool) → (A → Bool) → Set
  v f⊑ w = (a : _) → v a ⊑ w a ≡ true

open Func⊑ renaming (_f⊑_ to _⊑_) public

Minimal : {X : Set} (pred : (X → Bool) → Set) (v : X → Bool) → Set
Minimal {X} pred v = (w : X → Bool) → w Func⊑.f⊑ v → pred w → (x : X) → Bool= (v x) (w x) ≡ true

data 𝟚 : Set where
  𝟘 : 𝟚
  𝟙 : 𝟚

_⊚_ : {A : Set} {a b c : A} → a ≡ b → b ≡ c → a ≡ c
p ⊚ q = trans p q
infixr 20 _⊚_

Epi : ∀ {n m} {A : Set n} {B : Set m} → (A → B) → Set (n ⊔ m)
Epi {n} {m} {A} {B} f = (b : B) → Σ A (λ a → f a ≡ b)

Mono : ∀ {n m} {A : Set n} {B : Set m} → (A → B) → Set (n ⊔ m)
Mono {n} {m} {A} {B} f = (a₁ a₂ : A) → f a₁ ≡ f a₂ → a₁ ≡ a₂

_≅_ : ∀ {n m} (A : Set n) (B : Set m) → Set (n ⊔ m)
infix 5 _≅_
A ≅ B = Σ (A → B) (λ f → Epi f × Mono f)

-- f is an essentially isomorphism from A to (B st p)
IsoFor : {A B : Set} (f : A → B) (p : B → Set) → Set
IsoFor {A} {B} f p = (A ≅ B st p) st (λ cong → (a : A) → f a ≡ Item (proj₁ cong a))

≅sym : {A B : Set} → A ≅ B → B ≅ A
≅sym {A} {B} (f , (e , m)) = (λ b → proj₁ (e b)) , epiPf , monoPf where
  epiPf : (a : A) → Σ B (λ v → proj₁ (e v) ≡ a)
  epiPf = (λ a → (f a) , (m (proj₁ (e (f a))) a (proj₂ (e (f a)))))
  monoPf : Mono (λ b → proj₁ (e b))
  monoPf = λ a₁ a₂ eq → sym (proj₂ (e a₁)) ⊚ cong f eq ⊚ (proj₂ (e a₂))


isubst : ∀ {a p} {A : Set a} (P : A → Set p) {x y : A} → .(x ≡ y) → P x → P y
isubst P refl p = p

isubst-eq : ∀ {a p} {A : Set a} (P : A → Set p) {x y : A} (e1 e2 : x ≡ y) (p : P x)
  → isubst P e1 p ≡ isubst P e2 p
isubst-eq P refl refl p = refl

-- still can't see to define this:
{-
foo : (A B : Set) .(x : A) (f : A → B) (same : (a a' : A) → f a ≡ f a') → B
foo A B x f same = {!f x!}
-}
