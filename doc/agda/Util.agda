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

Balanced : {B : Set} → (B → Tern) → Set
Balanced {B} f = Uniq B (λ b → Tern= (f b) t+) ×
                 Uniq B (λ b → Tern= (f b) t-)

Triv : {B : Set} → (B → Tern) → Set
Triv {B} f = None B (λ b → Tern= (f b) t+) ×
             None B (λ b → Tern= (f b) t-)

NonTriv : {B : Set} → (B → Tern) → Set
NonTriv {B} f = One B (λ b → Tern= (f b) t+) ⊕
                One B (λ b → Tern= (f b) t-)

Calm : {B : Set} → (B → Tern) → Set
Calm {B} f = Balanced f ⊕ Triv f

_■_ : Tern → Tern → Bool
t0 ■ t = true
t+ ■ t+ = true
t- ■ t- = true
_ ■ _ = false

_⊑_ : {A : Set} → (A → Tern) → (A → Tern) → Set
v ⊑ w = (a : _) → v a ■ w a ≡ true
