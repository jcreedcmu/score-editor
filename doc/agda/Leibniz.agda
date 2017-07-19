{-# OPTIONS --without-K --rewriting --type-in-type #-}

module Leibniz where

open import HoTT

{- Here's Leibniz equality.
   Two things a and b are equal if for every property P that a satisfies, b satisfies it also. -}
module _ {A : Set} where
  _=#_ : (a b : A) → Set
  _=#_ a b = (P : A → Set) → P a → P b

{-
 What's an appropriate parametricity property for the type
   (P : A → Set) → P a → P b
 ? This can be fairly easily guessed without resorting to the full Atkey-Ghani-Johann sledgehammer.
 We just want to do the same thing we would do with (P : Set) → P → P but generalize over an index
 a ∈ A.

 So the relational parametricity property is:
 For every
  P1, P2 : A → Set
 and supposing every a ∈ A that there's a relation R a ⊆ P1 a × P2 a,
 if ℓ is an element of (P : A → Set) → P a → P b, then for any p1 ∈ P1 a and p2 ∈ P2 a such that p1 R p2,
 we have (ℓ P1 p1) R (ℓ P2 p2).

 Specializing this to functional relations --- that is, relations R
 defined by x R y ⇔ (f x == y) for some function
   f : {a : A} → P1 a → P2 a
 this property becomes

 If ℓ is an element of a =# b and p ∈ P1 a, then we have f (ℓ P1 p) = ℓ P2 (f p))
-}

{- Formally: -}
  postulate
    param : {P1 P2 : A → Set} {a b : A} (ℓ : a =# b) (p : P1 a) (f : {a : A} → P1 a → P2 a) → f (ℓ P1 p) == ℓ P2 (f p)

{- Armed with that we can show that Leibniz equality is the same thing as regular equality: -}
  into : {a b : A} → a == b → a =# b
  into idp P p = p

  out : {a b : A} → a =# b → a == b
  out {a} {b} ℓ = ℓ (a ==_) idp

  zig : {a b : A} (q : a == b) → out (into q) == q
  zig idp = idp

  zag : {a b : A} (ℓ : a =# b) → into (ℓ (a ==_ ) (idp {A = A})) == ℓ
  zag {a} {b} ℓ = param ℓ idp into ∙ λ= (λ P → λ= (λ p → param {P1 = (λ z → (P0 : A → Set) → P0 a → P0 z)} {P2 = P} ℓ (λ P p → p) (λ ℓ' → ℓ' P p)))

  thm : {a b : A} → (a == b) ≃ (a =# b)
  thm = equiv into out zag zig

{-
 Questions: (i) Are there suitable universe annotations to let me eliminate --type-in-type ?
                Or is only the universe-polymorphic leibniz equality actually equivalent to equality?
            (ii) Can I coalesce the two invocations of parametricity in zag to only one?
-}
