module FuncCellsHott where

open import HoTT hiding (ℤ ; ⊤ ; tt)

data ⊤ {a} : Set a where
  tt : ⊤

record _st_ {a b} (A : Set a) (B : A → Set b) : Set (lmax a b) where
  constructor _,,_
  field
    Item : A
    .Pf : B Item -- proof irrelevance
open _st_ public

data Gr : (C : Set) → Set₁ where
  gnil : Gr ⊤
  gcons : (C {D} : Set) (δ : C → D → Set) (G : Gr D) → Gr C

FibBelow : {C : Set} (G : Gr C) → Set₁
FibOver : {C : Set} (G : Gr C) → Set₁
FibBelow gnil = ⊤
FibBelow (gcons C δ G) = FibOver G
FibOver {C} G = (C → Set) × FibBelow G

φOver : {C : Set} (G : Gr C) (F : FibOver G) → Set₁
φOver gnil x = ⊤
φOver (gcons C {D} δ G) (cfib , F@(dfib , _)) = φOver G F × ((c : C) (d : D) → δ c d → cfib c → dfib d)

Dof : {C : Set} (G : Gr C) → Set
Dof gnil = ⊥
Dof (gcons C {D} δ _) = D

δof : {C : Set} (G : Gr C) → (C → Dof G → Set)
δof gnil c ()
δof (gcons C {D} δ _) = δ

DFibOf : {C : Set} {G : Gr C} → FibOver G → (Dof G → Set)
DFibOf {G = gnil} F ()
DFibOf {G = gcons C δ G} (_ , (dfib , _)) = dfib

DφOf : {C : Set} {G : Gr C} (F : FibOver G) (φ : φOver G F) → ((c : C) (d : Dof G) → δof G c d → fst F c → DFibOf F d)
DφOf {G = gnil} F φ c ()
DφOf {G = gcons C δ G} (cfib , F) (_ , φ) = φ


record PathsTo {C D E : Set} {c : C} (ν : Section) {e : E} (ε : DFibOf (fst oldcomp) e) : Set where
  inductive
    field
      d : D
      hop1 : δ c d
      hop2 : δ' d e
      trans : DφOf (fst oldcomp) (snd oldcomp) d e hop2 {!!} == ε

comp : (X : Set) {C : Set} (G : Gr C) → Σ (FibOver G) (φOver G)
comp X gnil = ((λ _ → X) , tt) , tt
{- comp X (gcons C {D} δ gnil) = (Section , fst oldcomp) , (snd oldcomp) , (λ c d m σ → σ d m) where
  oldcomp : Σ (FibOver gnil) (φOver gnil)
  oldcomp = comp X gnil

  Section : C → Set
  Section c = (d : ⊤) → δ c d → X -}


comp X (gcons C {D} δ G) = (Cfiber , fst oldcomp) , snd oldcomp , φ where
  oldcomp : Σ (FibOver G) (φOver G)
  oldcomp = comp X G
  E : Set
  E = Dof G
  δ' : D → E → Set
  δ' = δof G
  module Fixc (c : C) where
    Section : Set
    Section = (d : D) → δ c d → (fst (fst oldcomp)) d
    Calm : Section → Set
    Calm ν = (e : E) (ε1 ε2 : DFibOf (fst oldcomp) e) → PathsTo ν ε1 ≃ PathsTo ν ε2
  Cfiber : C → Set
  Cfiber c = Section st Calm where open Fixc c
  φ : (c : C) (d : D) → δ c d → Cfiber c → fst (fst oldcomp) d
  φ c d μ f = Item f d μ

{- module FixChain (χ : Chain) (Charge : Set) where
  open Chain χ
  F : {n : ℕ} (z : 𝕐 n) → Set
  Fsuc : {n : ℕ} (g : 𝕐 (S n)) → Set -- split this out to satisfy termination checker
  φ : {n : ℕ} {g : 𝕐 (S n)} → F {S n} g → (z : 𝕐 n) → δ n g z → F {n} z

  F {0} ()
  F {S n} g = Fsuc {n} g

  module FixN (n : ℕ) (c : 𝕐 (S (S n))) where
    ℂ = 𝕐 (S (S n))
    𝔾 = 𝕐 (S n)
    ℤ = 𝕐 n
    Section : Set
    Section = (g : 𝔾) → δ (S n) c g → Fsuc {n} g
    record PathsTo (ν : Section) {z : ℤ} (z' : F {n} z) : Set where
      field
        g : 𝔾
        hop1 : δ (S n) c g
        hop2 : δ n g z
        trans : φ (ν g hop1) z hop2 == z'
    Calm : Section → Set
    Calm ν = (z : ℤ) (z1' z2' : F {n} z) → PathsTo ν z1' ≃ PathsTo ν z2' where

  Fsuc {0} tt = Charge
  Fsuc {S n} c = Section st Calm where open FixN n c
  φ {0} g' ()
  φ {S n} = Item
-}
