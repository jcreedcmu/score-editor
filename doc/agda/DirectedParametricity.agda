module DirectedParametricity where

open import Level
open import Data.Unit hiding (_≤_)
open import Data.Product
open import Function

_⇒_ : ∀ {n m} → Set n → Set m → Set (n ⊔ m)
X ⇒ Y = (X → Y) × ⊤

_#_ : ∀ {n m} {X : Set n} {Y : Set m} → X ⇒ Y → X → Y
(f , tt) # x = f x

_∘∘_ : ∀ {n m p} {X : Set n} {Y : Set m} {Z : Set p} → Y ⇒ Z → X ⇒ Y → X ⇒ Z
(f , tt) ∘∘ (g , tt) = (f ∘ g , tt)

comb : ∀ {n m p} {X : Set n} {Y : Set m} {Z : Set p} → X → Y ⇒ Z → (X ⇒ Y) ⇒ Z
comb x (f , tt) = ((λ g → f (g # x)) , tt)

_≤_ : ∀ {n} {A : Set n} (a b : A) → Set (suc n)
_≤_ {n} {A} a b = (C : A ⇒ Set n) → C # a → C # b

Id : (A : Set) (x : A) → x ≤ x
Id A x C k = k

_⊚_ : {A : Set} {x y z : A} → y ≤ z → x ≤ y → x ≤ z
ℓ1 ⊚ ℓ2 = λ C k → ℓ1 C (ℓ2 C k)

functor : {A B : Set} (f : A ⇒ B) {a1 a2 : A} → a1 ≤ a2 → (f # a1) ≤ (f # a2)
functor f ℓ C k = ℓ (C ∘∘ f) k

nat1 : {A B : Set} {f g : A ⇒ B} (η : f ≤ g) (a : A) → (f # a) ≤ (g # a)
nat1 η a C k = η (comb a C) k

{-
functor F (Id ℂ X)
= λ C k → (Id ℂ X) (C ∘∘ F) k
= λ C k → (λ C' k' → k') (C ∘∘ F) k
= λ C k → k
= Id 𝔻 (F # X)
-}
functor-id : (ℂ 𝔻 : Set) (F : ℂ ⇒ 𝔻) (X : ℂ) → functor F (Id ℂ X) ≤ Id 𝔻 (F # X)
functor-id ℂ 𝔻 F X C k = k

functor-id2 : (ℂ 𝔻 : Set) (F : ℂ ⇒ 𝔻) (X : ℂ) → Id 𝔻 (F # X) ≤ functor F (Id ℂ X)
functor-id2 ℂ 𝔻 F X C k = k

functor-comp : (ℂ 𝔻 : Set) (F : ℂ ⇒ 𝔻) (X Y Z : ℂ) (g : Y ≤ Z) (f : X ≤ Y) → (functor F (g ⊚ f)) ≤ ((functor F g) ⊚ (functor F f))
functor-comp ℂ 𝔻 F X Y Z g f C k = k

{-
Goal: C # (functor G f ⊚ nat1 η A)
k : C # (nat1 η B ⊚ functor F f)

nat1 η B ⊚ functor F f
= λ C k → nat1 η B C (functor F f C k)
= λ C k → nat1 η B C (f (C ∘∘ F) k)
= λ C k → η (comb B C) (f (C ∘∘ F) k)

functor G f ⊚ nat1 η A
= λ C k → functor G f C (nat1 η A C k)
= λ C k → functor G f C (η (comb A C) k)
= λ C k → f (C ∘∘ G) (η (comb A C) k)
-}
nat2 : (ℂ 𝔻 : Set) (F G : ℂ ⇒ 𝔻) (η : F ≤ G) (A B : ℂ) (f : A ≤ B) → (nat1 η B ⊚ functor F f) ≤ (functor G f ⊚ nat1 η A)
nat2 ℂ 𝔻 F G η A B f C k = {!!}


{-
λ C₁ k₁ →
  η ((λ g → proj₁ C₁ (proj₁ g B)) , tt)
  (f ((λ x → proj₁ C₁ (proj₁ F x)) , tt) k₁)
-}
