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

Epi : {A B : Set} → (A → B) → Set
Epi {A} {B} f = (b : B) → Σ A (λ a → f a ≡ b)

Mono : {A B : Set} → (A → B) → Set
Mono {A} {B} f = (a₁ a₂ : A) → f a₁ ≡ f a₂ → a₁ ≡ a₂

_⊚_ : {A : Set} {a b c : A} → a ≡ b → b ≡ c → a ≡ c
p ⊚ q = trans p q
infixr 20 _⊚_

_≅_ : (A B : Set) → Set
infix 5 _≅_
A ≅ B = Σ (A → B) (λ f → Epi f × Mono f)

≅sym : {A B : Set} → A ≅ B → B ≅ A
≅sym {A} {B} (f , (e , m)) = (λ b → proj₁ (e b)) , epiPf , monoPf where
  epiPf : (a : A) → Σ B (λ v → proj₁ (e v) ≡ a)
  epiPf = (λ a → (f a) , (m (proj₁ (e (f a))) a (proj₂ (e (f a)))))
  monoPf : Mono (λ b → proj₁ (e b))
  monoPf = λ a₁ a₂ eq → sym (proj₂ (e a₁)) ⊚ cong f eq ⊚ (proj₂ (e a₂))
