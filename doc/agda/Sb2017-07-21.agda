{-# OPTIONS --without-K --rewriting #-}

module Sb2017-07-21 where

open import HoTT hiding ( Rel ; S )

module _ where

  Rel : Set → Set → Set₁
  Rel A B = A → B → Set

  Conv : {A B : Set} → Rel A B → Rel B A
  Conv R = (λ b a → R a b)

  Comp : {A B C : Set} → Rel A B → Rel B C → Rel A C
  Comp {A} {B} {C} R S a c = Σ B (λ b → R a b × S b c)

  Le : {A B : Set} → Rel A B → Rel A B → Set
  Le {A} {B} R S = (a : A) (b : B) → R a b → S a b

  Idr : {A : Set} → Rel A A
  Idr a b = a == b

  Adj : {A B : Set} → Rel A B → Set
  Adj R = (Le Idr (Comp R (Conv R))) × (Le (Comp (Conv R) R) Idr)

  isFunc : {A B : Set} → Rel A B → Set
  isFunc {A} {B} R = (a : A) → is-contr (Σ B (R a))

  into : {A B : Set} (R : Rel A B) → Adj R → isFunc R
  into {A} {B} R (η , ε) a = (η a a idp .fst , η a a idp .snd .fst) , {!ε!} where
    x : (b1 b2 : B) → Σ A (λ a → (R a b1) × (R a b2)) → b1 == b2
    x = ε
{-
η : 1A → Rop ∘ R
ε : R ∘ Rop → 1B
  thm :
-}
{-
  foo : (ι : ⊤ → B) (χ : ⊤) (ρ1 ρ2 : Σ B (λ b → b == ι χ)) → ρ1 == ρ2
  foo ι χ (_ , idp) (_ , idp) = idp


  is-contr-is-⊤ : {A : Set} → is-contr A → ⊤ == A
  is-contr-is-⊤ ic = ua (equiv (λ _ → ic .fst) (λ _ → tt) (ic .snd) (λ _ → idp)) where

  foo2 : {R : B → Set} (ic : is-contr (Σ B R)) (π : Σ B R → B) (χ : Σ B R) (ρ1 ρ2 : Σ B (λ b → b == π χ))  → ρ1 == ρ2
  foo2 ic = transport (λ z → (π : z → B) (χ : z) (ρ1 ρ2 : Σ B (λ b → b == π χ)) → ρ1 == ρ2) (is-contr-is-⊤ ic) foo

  foo⊤ : (π : ⊤ → B) (b : B) (ρ1 ρ2 : Σ ⊤ (λ p → π p == b))  → ρ1 == ρ2
  foo⊤  = {!!}

  foo9 : {R : B → Set} (ic : is-contr (Σ B R)) (π : Σ B R → B) (b : B) (ρ1 ρ2 : Σ (Σ B R) (λ p → π p == b))  → ρ1 == ρ2
  foo9 ic = {!!}

  foo3 : {R : B → Set} (ic : is-contr (Σ B R)) (χ : Σ B R) (ρ1 ρ2 : Σ B (λ b → b == fst χ))  → ρ1 == ρ2
  foo3 ic χ ρ1 ρ2  = foo2 ic fst χ ρ1 ρ2

-}
