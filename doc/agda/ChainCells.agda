module ChainCells (A : Set) where

-- open import Level renaming (suc to lsuc) hiding (zero)
open import Data.Integer renaming (suc to isuc ; _+_ to _i+_ ; _*_ to _i*_ ) hiding ( _⊔_ )
open import Data.Nat hiding ( _⊔_ )
open import Data.Unit
open import Data.Empty
open import Data.Bool
open import Data.Sum renaming ( _⊎_ to _⊕_ )
open import Data.Product
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Level hiding ( zero ) renaming (suc to lsuc)
open import Function
open import Data.Fin hiding (_+_ ; #_)

record _st_{a b} (A : Set a) (B : A → Set b) : Set (a ⊔ b) where
  constructor _,,_
  field
    Item : A
    .Pf : B Item -- proof irrelevance
open _st_

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


𝔻 : ((n : ℕ) → Set) → (n : ℕ) → Set
𝔻 ℂ zero = ⊤
𝔻 ℂ (suc n) = ℂ n

record Chain : Set₁ where
  constructor MkChain
  field
    ℂ : (n : ℕ) → Set
    δ : (n : ℕ) → ℂ n → 𝔻 ℂ n → Tern

isZeroCover : (χ : Chain) (n : ℕ) → (Chain.ℂ χ n → Tern) → Set
isZeroCover (MkChain ℂ δ) n v = (c : 𝔻 ℂ n) → calm (λ e → v e ** δ n e c)

GoodCell : {n : ℕ} (χ : Chain) (c : Chain.ℂ χ (suc n)) → Set
GoodCell {n} χ@(MkChain ℂ δ) c = isZeroCover χ n (δ (suc n) c)

Good : Chain → Set
Good χ@(MkChain ℂ δ) = (n : ℕ) (c : ℂ (suc n)) → GoodCell χ c

{--- an attempt to do bundle style development here ---}

record Bundle : Set₁ where
  constructor MkBundle
  field
    𝔾 : Set
    ℂ : Set
    ∂ : ℂ → 𝔾 → Tern

ZeroFunc : (β : Bundle) → (Bundle.ℂ β → Tern) → Set
ZeroFunc (MkBundle 𝔾 ℂ ∂) v = (g : 𝔾) → calm (λ e → v e ** ∂ e g)

OkayFunc : (β : Bundle) (v : Bundle.ℂ β → Tern) → Set
OkayFunc β v = ZeroFunc β v × NonTriv v

_■_ : Tern → Tern → Bool
t0 ■ t = true
t+ ■ t+ = true
t- ■ t- = true
_ ■ _ = false

_⊑_ : {A : Set} → (A → Tern) → (A → Tern) → Set
v ⊑ w = (a : _) → v a ■ w a ≡ true

MinimalFunc : {X : Set} (pred : (X → Tern) → Set) (v : X → Tern) → Set
MinimalFunc {X} pred v = (w : X → Tern) → w ⊑ v → pred w → (x : X) → Tern= (v x) (w x) ≡ true

GoodFunc : (β : Bundle) (v : Bundle.ℂ β → Tern) → Set
GoodFunc β v = OkayFunc β v × MinimalFunc (OkayFunc β) v

IncBundle : Bundle → Bundle
IncBundle β@(MkBundle 𝔾 ℂ ∂) = MkBundle ℂ ((ℂ → Tern) st (GoodFunc β)) Item

GiveBundle : ℕ → Bundle
GiveBundle zero = MkBundle ⊤ A (λ a _ → t+)
GiveBundle (suc n) = IncBundle (GiveBundle n)
