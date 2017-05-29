{-# OPTIONS --without-K --rewriting #-}

open import TopCells
open import HoTT hiding ( _$_ ; north ; south ) renaming ( Type to _Type )

module TopCellsPf where

{-

Here I tried proving that
    Model ○gr X ≃ ○ → X
directly, but got a little discouraged at the complexity of it.

Maybe try proving more directly that the "type" Model ○gr
has the expected universal property of ○?

-}

modelInCirc : Model ○gr ○
modelInCirc = record { point = point ; cell = cell } where
  open Graph ○gr
  point : 𝕍 → ○
  point vn = north
  point vs = south
  point ve = (pointOfPath east)
  point vw = (pointOfPath west)

  cell : (v : 𝕍) → ==i (point v) (λ (we : Σ 𝕍 (𝔼 v)) → point (fst we))
  cell v =  coe (ap (==i (point v)) (λ= (subgoal v))) refli where
    subgoal : (v : 𝕍) (we : Σ 𝕍 (𝔼 v)) → point v == point (fst we)
    subgoal ve (vn , ene) = pointOfPathDom east
    subgoal ve (vs , ese) = pointOfPathCod east
    subgoal vw (vn , enw) = pointOfPathDom west
    subgoal vw (vs , esw) = pointOfPathCod west
    -- note no cases for subgoal vn, subgoal vs

thm : (X : Set) → Model ○gr X ≃ (○ → X)
thm X = modelToLoop , record { g = loopToModel ; f-g = f-g ; g-f = g-f ; adj = adj } where
  modelToLoop : Model ○gr X → ○ → X
  modelToLoop M = ○-elim  {λ x → X} (point vn) (point vs) eastEdge westEdge where
    open Model M
    eastEdge = pathToOver east (graphPath M vn vs ve ene ese)
    westEdge = pathToOver west (graphPath M vn vs vw enw esw)

  loopToModel : (○ → X) → Model ○gr X
  loopToModel f = record { point = λ v → f (point v) ; cell = λ v → api f (cell v) } where
    open Model modelInCirc

  f-g : (f : ○ → X) → modelToLoop (loopToModel f) == f
  f-g f = λ= lemma where
    lemma : (c : ○) → modelToLoop (loopToModel f) c == f c
    lemma = {!!} -- use ○ induction

  g-f : (M : Model ○gr X) → loopToModel (modelToLoop M) == M
  g-f record { point = point ; cell = cell } = {!!}

  adj : (a : Model ○gr X) →
        ap modelToLoop (g-f a) == f-g (modelToLoop a)
  adj = {!!}
