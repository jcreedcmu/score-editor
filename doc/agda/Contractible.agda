{-# OPTIONS --without-K --rewriting #-}

module Contractible where

open import HoTT hiding ( Type ; _$_ )

Type = Type0

idp[] : {A : Type} (a b : A) (path : a == b) → idp == path [ (λ c → a == c) ↓ path ]
idp[] a b idp = idp

lemmaU : (sp : Span)
         (ca : Span.A sp == ⊤) (cb : Span.B sp == ⊤) (cc : Span.C sp == ⊤)
        → is-contr (Pushout sp)
lemmaU sp idp idp idp = (left tt) , Pushout-elim left* right* glue* where
  open Span sp
  left* : (a : ⊤) → left tt == left a
  left* tt = idp
  right* : (b : ⊤) → left tt == right b
  right* tt  = glue tt
  glue* : (c : ⊤) → left* tt == right* tt [ (λ z → left tt == z) ↓ glue c ]
  glue* tt = idp[] (left tt) (right tt) (glue tt)

{-
  Two contractible spaces, glued together by a contractible space, yield a contractible space
-}

thmU : (sp : Span {lzero} {lzero} {lzero})
  → is-contr (Span.A sp)
  → is-contr (Span.B sp)
  → is-contr (Span.C sp)
  → is-contr (Pushout sp)
thmU sp ca cb cc =
  lemmaU sp
    (ua (contr-equiv-Unit ca))
    (ua (contr-equiv-Unit cb))
    (ua (contr-equiv-Unit cc))
  where open Span sp
