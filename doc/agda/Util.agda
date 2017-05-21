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

one : (B : Set) → (B → Bool) → Set
one B pred = Σ B (λ b → (pred b ≡ true))

uniq : (B : Set) → (B → Bool) → Set
uniq B pred = Σ B (λ b → (pred b ≡ true) × ((b' : B) → pred b' ≡ true → b ≡ b'))

none : (B : Set) → (B → Bool) → Set
none B pred = (b : B) → pred b ≡ false

balanced : {B : Set} → (B → Tern) → Set
balanced {B} f = uniq B (λ b → Tern= (f b) t+) ×
                 uniq B (λ b → Tern= (f b) t-)

null : {B : Set} → (B → Tern) → Set
null {B} f = none B (λ b → Tern= (f b) t+) ×
             none B (λ b → Tern= (f b) t-)

calm : {B : Set} → (B → Tern) → Set
calm {B} f = balanced f ⊕ null f

NonTriv : {B : Set} → (B → Tern) → Set
NonTriv {B} f = one B (λ b → Tern= (f b) t+) ⊕
                one B (λ b → Tern= (f b) t-)

_■_ : Tern → Tern → Bool
t0 ■ t = true
t+ ■ t+ = true
t- ■ t- = true
_ ■ _ = false

_⊑_ : {A : Set} → (A → Tern) → (A → Tern) → Set
v ⊑ w = (a : _) → v a ■ w a ≡ true
