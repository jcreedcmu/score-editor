{-# OPTIONS --without-K --rewriting  #-}
module _ where

open import HoTT

postulate
  ○ : ∀ {n} → Set n → Set (lmax n (lsucc lzero))
  fmap : ∀ {n m} {X : Set m} {Y : Set n} → (X → Y) → ○ X → ○ Y
  η : ∀ {n} {X : Set n} → X → ○ X
  μ : ∀ {n} {X : Set n} → ○ (○ X) → ○ X
  idℓ : {X : Set} (x : ○ X) → μ (η x) == x
  idr : {X : Set} (x : ○ X) → μ (fmap η x) == x
  assoc : {X : Set} (x : ○ (○ (○ X))) → μ (μ x) == μ (fmap μ x)

  _#_ : ∀ {n} {A : Set n} → A → A → Set
  #refl : ∀ {n} {A : Set n} (x : A) → x # x
  #J : ∀ {n} {A : Set n} {x : A} (P : (y : A) (b : x # y) → Set) → P x (#refl x) → ((y : A) (b : x # y) → P y b)

  _~_ : ∀ {n} {A : Set n} → ○ A → ○ A → Set
  ~refl : ∀ {n} {A : Set n} (x : ○ A) → x ~ x
  ~J : ∀ {n m} {A : Set n} {x : ○ A} (P : (y : ○ A) (b : x ~ y) → Set m) → P x (~refl x) → ((y : ○ A) (b : x ~ y) → P y b)

bind : ∀ {n m} {B : Set n} {C : Set m} → ○ B → (B → ○ C) → ○ C
bind e k = μ (fmap k e)

#rec : ∀ {n} {A : Set n} {x y : A} (P : A → Set) → x # y → P x → P y
#rec {y = y} P b px = #J (λ y b → P y) px y b

~rec : ∀ {n m} {A : Set n} {x y : ○ A} (P : ○ A → Set m) → x ~ y → P x → P y
~rec {y = y} P b px = ~J (λ y b → P y) px y b

#rev : ∀ {n} {A : Set n} {x y : A} → x # y → y # x
#rev {x = x} {y} b = #rec (λ z → z # x) b (#refl x)

~rev : ∀ {n} {A : Set n} {x y : ○ A} → x ~ y → y ~ x
~rev {x = x} {y} b = ~rec (λ z → z ~ x) b (~refl x)

#comp : ∀ {n} {A : Set n} {x y z : A} → y # z → x # y → x # z
#comp {x = x} {y} {z} b c = #rec (λ w → x # w) b c

~comp : ∀ {n} {A : Set n} {x y z : ○ A} → y ~ z → x ~ y → x ~ z
~comp {x = x} {y} {z} b c = ~rec (λ w → x ~ w) b c

#trans : ∀ {n} {A B : Set n} {x y : A} (f : A → B) → x # y → f x # f y
#trans {x = x} {y} f b = #rec (λ z → f x # f z) b (#refl (f x))

~trans : ∀ {n} {A B : Set n} {x y : A} (f : A → B) → (η x) ~ (η y) → fmap f (η x) ~ fmap f (η y)
~trans {x = x} {y} f b = ~rec (λ z → fmap f (η x) ~ fmap f z) b (~refl (fmap f (η x)))

guess2 : {A : Set} {x y : ○ A} → x == y → x ~ y
guess2 idp = ~refl _

guess : {A : Set} {x y : A} → η x == η y → (η x ~ η y)
guess b = guess2 b

rguess : {A : Set} {x y : ○ A} → (x ~ y) → x == y
rguess {A} {x} {y} b = ~rec (λ z → x == z) b idp
