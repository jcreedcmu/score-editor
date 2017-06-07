module FuncCellsHott where

open import HoTT hiding (ℤ ; ⊤ ; tt)

record Gr : Set₁ where
  constructor MkG
  field
    C : Set
    δ : C → C → Set

record Mod (G : Gr) : Set₁ where
  constructor MkMod
  open Gr G
  field
    F : C → Set
    φ : (c : C) (fc : F c) (d : C) (μ : δ c d) → F d

record _st_ {a b} (A : Set a) (B : A → Set b) : Set (lmax a b) where
  constructor _,,_
  field
    Item : A
    .Pf : B Item -- proof irrelevance
open _st_ public

module Fix {G : Gr} (M : Mod G) (c : Gr.C G) where
  open Gr G
  open Mod M

  Section : Set
  Section = (d : C) → δ c d → F d

  record PathsTo {z : C} (ν : Section) (ζ : F z) : Set where
    field
      g : C
      hop1 : δ c g
      hop2 : δ g z
      trans : φ g (ν g hop1) z hop2 == ζ

  CalmSections : Σ Set (λ S → S → Section)
  CalmSections = (Section st (λ ν → (z : C) (ζ1 ζ2 : F z) → PathsTo ν ζ1 ≃ PathsTo ν ζ2)) , Item

  GoodAt : Set₁
  GoodAt = CalmSections == (F c , φ c)
open Fix

GoodMod : (G : Gr)  → Set₁
GoodMod G = Σ (Mod G) (λ M → (c : _) → GoodAt M c)
