{-# OPTIONS --without-K --rewriting #-}

open import HoTT hiding (Bool ; true ; false ; _$_)

module Asdf where

record Gr : Set₁ where
  constructor MkGr
  field
    C : Set
    R : C → C → Set
    id : (c : C) → R c c

record GrM (G1 : Gr) (G2 : Gr) : Set where
  constructor MkGrM
  open Gr
  field
    Cm : C G1 → C G2
    Rm : (c d : C G1) → R G1 c d → R G2 (Cm c) (Cm d)
    idm : (c : C G1) → Rm c c (id G1 c) == id G2 (Cm c)

Prod : Gr → Gr → Gr
Prod (MkGr C1 R1 id1) (MkGr C2 R2 id2) = MkGr (C1 × C2) (λ { (c1 , c2) (d1 , d2) → R1 c1 d1 × R2 c2 d2 }) (λ { (c1 , c2) → (id1 c1) , (id2 c2) })

data TripV : Set where
  dom : TripV
  cod : TripV

data TripE : TripV → TripV → Set where
  ef : TripE dom cod
  ecod : TripE cod cod
  edom : TripE dom dom

TripId : (v : TripV) → TripE v v
TripId dom = edom
TripId cod = ecod

Triple : Gr
Triple = MkGr TripV TripE TripId

Exp : Gr → Gr → Gr
Exp G1@(MkGr C1 R1 id1) G2@(MkGr C2 R2 id2) = MkGr C R id where
  C = GrM G1 G2
  R = λ M1 M2 → (c d : C1) (e : R1 c d) → R2 (GrM.Cm M1 c) (GrM.Cm M2 d)
  id = GrM.Rm
