module Util where
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

data Tern : Set where
 t+ : Tern
 t- : Tern
 t0 : Tern

Tern= : Tern → Tern → Bool
Tern= t+ t+ = true
Tern= t- t- = true
Tern= t0 t0 = true
Tern= _ _ = false

_**_ : Tern -> Tern -> Tern
t0 ** _ = t0
_ ** t0 = t0
t+ ** x = x
x ** t+ = x
t- ** t- = t+

One : (B : Set) → (B → Bool) → Set
One B pred = Σ B (λ b → (pred b ≡ true))

Uniq : (B : Set) → (B → Bool) → Set
Uniq B pred = Σ B (λ b → (pred b ≡ true) × ((b' : B) → pred b' ≡ true → b ≡ b'))

None : (B : Set) → (B → Bool) → Set
None B pred = (b : B) → pred b ≡ false

Combi : (prop : (B : Set) → (B → Bool) → Set) (combiner : Set → Set → Set) → {B : Set} → (B → Tern) → Set
Combi prop combiner {B} f = combiner (prop B (λ b → Tern= (f b) t+)) (prop B (λ b → Tern= (f b) t-))

Balanced = Combi Uniq _×_
Triv = Combi None _×_
NonTriv = Combi One _⊕_

Calm : {B : Set} → (B → Tern) → Set
Calm {B} f = Balanced f ⊕ Triv f

module Tern⊑ where
  _⊑_ : Tern → Tern → Bool
  t0 ⊑ t = true
  t+ ⊑ t+ = true
  t- ⊑ t- = true
  _ ⊑ _ = false
open Tern⊑

module Func⊑ where
  _f⊑_ : {A : Set} → (A → Tern) → (A → Tern) → Set
  v f⊑ w = (a : _) → v a ⊑ w a ≡ true

open Func⊑ renaming (_f⊑_ to _⊑_) public
