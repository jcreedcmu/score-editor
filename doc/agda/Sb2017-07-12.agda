{-# OPTIONS --without-K --rewriting #-}

module Sb2017-07-12 where

open import HoTT

Σ' = Σ
syntax Σ' A (λ x → B) = ∃ x [ A ] B

qinv : {A B : Set} (f : A → B) → Set
qinv {A} {B} f = ∃ g [ (B → A) ] ∃ zig [ f ∘ g ∼ idf B ] (g ∘ f ∼ idf A)


record Inv {A B : Set} (f : A → B) : Set where
  field
    ι : B → A
    zig : f ∘ ι == idf B
    zag : ι ∘ f == idf A

record Binv {A B : Set} (f : A → B) : Set where
  field
    g h : B → A
    bzig : f ∘ g == idf B
    bzag : h ∘ f == idf A


Section : {A B : Set} (f : A → B) → Set
Section {A} {B} f = ∃ g [ (B → A) ] g ∘ f == idf A

thm : {A B : Set} (f : A → B) → (p q : Section f) → p == q
thm f (g , p) (h , q) = {!!}
