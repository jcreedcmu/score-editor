{-# OPTIONS --without-K --rewriting #-}

module TopCells where

open import HoTT hiding ( _$_ ; north ; south ) renaming ( Type to _Type )

{--- general way of specifying HITs? ---}

record Graph : Set₁ where
  constructor MkGraph
  field
    𝕍 : Set
    𝔼 : 𝕍 → 𝕍 → Set

data ==i {A : Set} {B : Set} : B → (f : A → B) → Set where
  refli : {b : B} → ==i b (λ _ → b)
-- (==i b (λ a → f a) means "b and all the f a are simultaneously equal")

module FixGraph (χ : Graph) (X : Set) where
  open Graph χ

  record Model : Set where
    field
      point : 𝕍 → X
      cell : (v : 𝕍) → ==i (point v) (λ (we : Σ 𝕍 (𝔼 v)) → point (fst we))
open FixGraph

{--- define the circle via some cells ---}

data ○vert : Set where
  vn vs ve vw : ○vert

data ○edge : ○vert → ○vert → Set where
  enw : ○edge vw vn
  esw : ○edge vw vs
  ene : ○edge ve vn
  ese : ○edge ve vs

○gr : Graph
○gr = MkGraph ○vert ○edge

{--- define the circle in a way that is hopefully convenient ---}

module _ where

  postulate  -- HIT
    ○ : Set

  module _ where

    postulate  -- HIT
      north south : ○
      east west : north == south

  module ○Elim {P : ○ → Set}
    (n* : P north)
    (s* : P south)
    (e* : n* == s*  [ P ↓ east ])
    (w* : n* == s*  [ P ↓ west ]) where

    postulate  -- HIT
      f : Π (○) P
      n-β : f north ↦ n*
      s-β : f south ↦ s*
    {-# REWRITE n-β #-}
    {-# REWRITE s-β #-}

    postulate -- HIT
      e-β : apd f east ↦ e*
      w-β : apd f west ↦ w*
    {-# REWRITE e-β #-}
    {-# REWRITE w-β #-}

○-elim = ○Elim.f

{--- some lemmas ---}

pathToOver : {A X : Set} {a b : A} {x y : X} (p : a == b) → x == y → x == y [ (λ _ → X) ↓ p ]
pathToOver idp idp = idp

pointOfPath : {A : Set} {a b : A} → a == b → A
pointOfPath {A} {a} {.a} idp = a

pointOfPathDom : {A : Set} {a b : A} (p : a == b) → pointOfPath p == a
pointOfPathDom {A} {a} {.a} idp = idp

pointOfPathCod : {A : Set} {a b : A} (p : a == b) → pointOfPath p == b
pointOfPathCod {A} {a} {.a} idp = idp

module FixModel {χ : Graph} {X : Set} (M : Model χ X) where
  open Graph χ
  open Model M

  graphPath : (va vb vm : 𝕍) (dom : 𝔼 vm va) (cod : 𝔼 vm vb) → point va == point vb
  graphPath va vb vm dom cod = lemma va vb vm (λ we → point (fst we)) dom cod (cell vm) where
    lemma : (va vb vm : 𝕍) (f : (Σ 𝕍 (𝔼 vm)) → X) (dom : 𝔼 vm va) (cod : 𝔼 vm vb) → ==i (point vm) f → f (va , dom) == f (vb , cod)
    lemma va vb vm f dom cod refli = idp
open FixModel

{--- prove them equiv ---}

thm : (X : Set) → Model ○gr X ≃ (○ → X)
thm X = modelToCirc , record { g = circToModel ; f-g = {!f-g!} ; g-f = {!!} ; adj = {!!} } where
  open Graph ○gr

  modelToCirc : Model ○gr X → ○ → X
  modelToCirc M = ○-elim  {λ x → X} (point vn) (point vs) eastEdge westEdge where
    open Model M
    eastEdge = pathToOver east (graphPath M vn vs ve ene ese)
    westEdge = pathToOver west (graphPath M vn vs vw enw esw)

  circToModel : (○ → X) → Model ○gr X
  circToModel f = record { point = point ; cell = cell } where
    point : 𝕍 → X
    point vn = f north
    point vs = f south
    point ve = f (pointOfPath east)
    point vw = f (pointOfPath west)

    cell : (v : 𝕍) → ==i (point v) (λ (we : Σ 𝕍 (𝔼 v)) → point (fst we))
    cell v =  coe (ap (==i (point v)) (λ= (subgoal v))) refli where
      subgoal : (v : 𝕍) (we : Σ 𝕍 (𝔼 v)) → point v == point (fst we)
      subgoal ve (vn , ene) = ap f (pointOfPathDom east)
      subgoal ve (vs , ese) = ap f (pointOfPathCod east)
      subgoal vw (vn , enw) = ap f (pointOfPathDom west)
      subgoal vw (vs , esw) = ap f (pointOfPathCod west)
      -- note no cases for subgoal vn, subgoal vs


  f-g : (b : ○ → X) → modelToCirc (circToModel b) == b
  f-g = {!!}
