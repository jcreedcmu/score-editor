{-# OPTIONS --without-K --rewriting #-}

module Contractible where

open import HoTT hiding ( Type ; _$_ )

Type = Type0

-- Contractible space
Cbl : Type → Type
Cbl A = Σ A (λ a → (a' : A) → a == a')

thru : {A : Type} → Cbl A → (a a' : A) → a == a'
thru cbl a a' = ! (snd cbl a) ∙ (snd cbl a')

thruLemma : {A : Type} (cbl : Cbl A) (a1 a2 : A) (p : a1 == a2) → thru cbl a1 a2 == p
thruLemma cbl a1 a2 idp = !-inv-l (snd cbl a1)

pathCbl : {A : Type} (cbl : Cbl A) (a1 a2 : A) → Cbl (a1 == a2)
pathCbl cbl a1 a2 = (thru cbl a1 a2) , (thruLemma cbl a1 a2)

thru-ap : (A C : Type) (ca : Cbl A) (cc : Cbl C) (c1 c2 : C) (f : C → A)
  → thru ca (f c1) (f c2) == ap f (thru cc c1 c2)
thru-ap A C ca cc c1 c2 f = thru (pathCbl ca (f c1) (f c2)) (thru ca (f c1) (f c2)) (ap f (thru cc c1 c2))

ap∘ : {A B C : Type} {x y : A} (f : B → C) (g : A → B) (p : x == y) → ap f (ap g p) == ap (f ∘ g) p
ap∘ f g idp = idp

idp[] : {A : Type} ($$ a : A) (path : $$ == a) → idp == path [ (λ a' → $$ == a') ↓ path ]
idp[] $$ a idp = idp

{-
  Two contractible spaces, glued together by a contractible space, yield a contractible space
-}

thm : (sp : Span)
  → Cbl (Span.A sp)
  → Cbl (Span.B sp)
  → Cbl (Span.C sp)
  → Cbl (Pushout sp)

thm sp ca cb cc = $ , pfPart where
  open Span sp

  {- the distinguished point of c that will be the distinguished witness of the contractibility of the pushout -}
  $c = fst cc

  $ : Pushout sp
  $ = left (f $c)

  joinA : (a : A) → $ == left a
  joinA a = ap left (thru ca (f $c) a)

  joinB : (b : B) → $ == right b
  joinB b = glue $c ∙ ap right (thru cb (g $c) b)

  module FixC (c : C) where
    w : $c == c
    w = thru cc $c c

    {- contract back to the id path for A... -}
    joinFirst : joinA (f c) == idp [ (λ a' → $ == a') ↓ ! (joinA (f c)) ]
    joinFirst = !ᵈ (idp[] $ (left (f c)) (joinA (f c)))

    {- contract back to the id path for B... -}
    joinSecond : idp == joinB (g c) [ (λ a' → $ == a') ↓ joinB (g c) ]
    joinSecond = idp[] $ (right (g c)) (joinB (g c))

    {- ...bash them together... -}
    joinMerge : joinA (f c) == joinB (g c) [ (λ a' → $ == a') ↓ (!(joinA (f c)) ∙ joinB (g c)) ]
    joinMerge = joinFirst ∙ᵈ joinSecond

   {- From now own only have to think hard about *non-*dependent equality, phew... -}
    A-lemma : joinA (f c) == ap (left ∘ f) (thru cc $c c)
    A-lemma = ap (ap left) (thru-ap A C ca cc $c c f) ∙ ap∘ left f (thru cc $c c)

    B-lemma : ap (right {d = sp}) (thru cb (g $c) (g c)) == ap (right ∘ g) (thru cc $c c)
    B-lemma = ap (ap right) (thru-ap B C cb cc $c c g) ∙ ap∘ right g (thru cc $c c)

    glueMerge : !(joinA (f c)) ∙ joinB (g c) == glue c
    glueMerge =
      !(joinA (f c)) ∙ joinB (g c)                                       =⟨ ap (λ z → !(z) ∙ joinB (g c)) A-lemma  ⟩
      !(ap (left ∘ f) w) ∙ joinB (g c)                                   =⟨ idp ⟩
      !(ap (left ∘ f) w) ∙ (glue $c ∙ ap right (thru cb (g $c) (g c)))   =⟨ ap (λ z → !(ap (left ∘ f) w) ∙ (glue $c ∙ z)) B-lemma ⟩
      !(ap (left ∘ f) w) ∙ (glue $c ∙ ap (right ∘ g) w)                  =⟨ C-lemma' w ⟩
      glue c ∎
      where
      C-lemma : (c1 c2 : C) (x : c1 == c2) → ! (ap (left ∘ f) x) ∙ (glue c1 ∙ ap (right ∘ g) x) == glue c2
      C-lemma c1 c2 idp = ∙-unit-r (glue c1)

      C-lemma' : (x : $c == c) → ! (ap (left ∘ f) x) ∙ (glue $c ∙ ap (right ∘ g) x) == glue c
      C-lemma' = C-lemma $c c

    {- transport along glueMerge to get the actual gluing clause for Pushout-elim -}
    joinGlue : joinA (f c) == joinB (g c) [ (λ a' → $ == a') ↓ glue c ]
    joinGlue = transport (λ z → joinA (f c) == joinB (g c) [ (λ a' → $ == a') ↓ z ]) glueMerge joinMerge

  open FixC
  pfPart : (a' : Pushout sp) → $ == a'
  pfPart = Pushout-elim {P = λ a' → $ == a'} joinA joinB joinGlue
