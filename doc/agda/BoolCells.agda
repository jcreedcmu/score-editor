module BoolCells where

open import Data.Nat
open import Data.Unit
open import Data.Bool
open import Data.Product
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; subst; sym; cong; trans)
open import Data.Empty
open import Data.Sum renaming ( _⊎_ to _⊕_ )
open import BoolUtil hiding (Calm)

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
A ≅ B = Σ (A → B) (λ f → Epi f × Mono f)

≅sym : {A B : Set} → A ≅ B → B ≅ A
≅sym {A} {B} (f , (e , m)) = (λ b → proj₁ (e b)) , epiPf , monoPf where
  epiPf : (a : A) → Σ B (λ v → proj₁ (e v) ≡ a)
  epiPf = (λ a → (f a) , (m (proj₁ (e (f a))) a (proj₂ (e (f a)))))
  monoPf : Mono (λ b → proj₁ (e b))
  monoPf = λ a₁ a₂ eq → sym (proj₂ (e a₁)) ⊚ cong f eq ⊚ (proj₂ (e a₂))

Doubleton : (B : Set) → Set
Doubleton B = 𝟚 ≅ B

2niq : (B : Set) → (B → Set) → Set
2niq B pred = Doubleton (B st pred)

𝔻 : ((n : ℕ) → Set) → (n : ℕ) → Set
𝔻 𝕏 zero = ⊤
𝔻 𝕏 (suc n) = 𝕏 n

record Chain : Set₁ where
  constructor MkChain
  field
    𝕏 : (n : ℕ) → Set
    δ : {n : ℕ} → 𝕏 n → 𝔻 𝕏 n → Bool

module _OverChain (χ : Chain) where
  open Chain χ
  record OverChain : Set₁ where
    constructor MkOverChain
    field
      𝕧 : (n : ℕ) → Set -- this is "(-1)-indexed": e.g. 𝕧 0 lives over the ⊤ inserted by 𝔻
      p : {n : ℕ} → 𝕧 n → 𝔻 𝕏 n -- this type realizes the above comment
      ∂ : {n : ℕ} → 𝕧 (suc n) → 𝕧 n → Bool
open _OverChain

module FixChains (χ : Chain) (π : OverChain χ) where
  open Chain χ
  open OverChain π

  -- XXX ?
  above : (n : ℕ) (g : 𝔻 𝕏 n) → Set
  above n g = (𝕧 n) st (λ v → p v ≡ g)

  module FixN (n : ℕ) where
    ℍ = 𝕏 (suc n)
    ℂ = 𝕏 n
    𝔾 = 𝔻 𝕏 n
    𝕘 = 𝕧 n
    𝕔 = 𝕧 (suc n)
    -- p : 𝕘 → 𝔾 , 𝕔 → ℂ

    Sectional : (c : ℂ) (ν : 𝕘 → Bool) → Set
    Sectional c ν = (g : 𝔾) → (if δ c g then ⊤ else ⊥) ≅ (𝕘 st (λ g' → (p g' ≡ g) × (ν g' ≡ true)))

    WholeFiber : ((B : Set) → (B → Bool) → Set) → (g : 𝔾) (ν : 𝕔 → Bool) → Set
    WholeFiber cond g ν = (g' : 𝕘) → p g' ≡ g → cond 𝕔 (λ c' → ν c' ∧ ∂ c' g')

    Calm : (ν : 𝕔 → Bool) → Set
    Calm ν = (g : 𝔾) → WholeFiber Uniq g ν ⊕ WholeFiber None g ν

  module PredCalm where
    open FixN
    PredCalm : (n : ℕ) (ν : 𝕧 n → Bool) → Set
    PredCalm zero ν = ⊤
    PredCalm (suc n) ν = Calm n ν
  open PredCalm

  module FixN2 (n : ℕ) where
    open FixN n
    GoodFunc : (c : ℂ) (ν : 𝕘 → Bool)  → Set
    GoodFunc c ν = Sectional c ν × PredCalm n ν
