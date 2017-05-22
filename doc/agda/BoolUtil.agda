module BoolUtil where
open import Level
open import Data.Bool
open import Data.Product
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
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
