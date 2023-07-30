module TopCellsPaths where

open import HoTT hiding (ℤ ; ⊤ ; tt)

record Gr : Set₁ where
  constructor MkG
  field
    C : Set
    δ : C → C → Set

BinRel : Set₁
BinRel = Σ Set (λ X → X → X → Set)

PathRel : (X : Set) → BinRel
PathRel X = X , _==_

record Mod (G : Gr) (X : Set) : Set₁ where
  constructor MkMod
  open Gr G
  field
    π : C → C → Set
    ε : {c d : C} (p1 p2 : π c d) → p1 == p2
    k : {c d e : C} (p1 : π c d) (p2 : π d e) → π c e
    μ : C → X
    ζ : {c d : C} (p1 : π c d) → μ c == μ d
    ℓ : {c d e : C} (p : π c d) (q : π d e) (r : π c e) → ζ r == ζ p ∙ ζ q

module Fix (G : Gr) (X : Set) (M : Mod G X) where
  open Gr G
  open Mod M

  thm : {!!}
  thm = {!!}


-- {c d e f : C} (cd : π c d) (de : π d e) (ef : π e f) (ce : π c e) (df : π d f) (cf : π c f)
--             → ζ (k p q) == ζ p ∙ ζ q
