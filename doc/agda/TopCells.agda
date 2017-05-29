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
open FixGraph public using ( Model )

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

api : {A B C : Set} {b : B} {k : A → B} (f : B → C) → ==i b k → ==i (f b) (f ∘ k)
api f refli = refli

module _Model= {χ : Graph} {X : Set}  where
  open Graph χ
  open Model
  Model= : {M1 M2 : Model χ X}
    (p : point M1 == point M2)
    (q : cell M1 == cell M2 [ (λ π → (v : 𝕍) → ==i (π v) (λ (we : Σ 𝕍 (𝔼 v)) → π (fst we))) ↓ p ])
    → M1 == M2
  Model= idp idp = idp
open _Model= public

module FixModel {χ : Graph} {X : Set} (M : Model χ X) where
  open Graph χ
  open Model M

  domPath : (va vm : 𝕍) (dom : 𝔼 vm va) → point va == point vm
  domPath va vm dom = lemma va vm (λ we → point (fst we)) dom (cell vm) where
    lemma : (va vm : 𝕍) (f : (Σ 𝕍 (𝔼 vm)) → X) (dom : 𝔼 vm va) → ==i (point vm) f → f (va , dom) == point vm
    lemma va vm f dom refli = idp

  graphPath : (va vb vm : 𝕍) (dom : 𝔼 vm va) (cod : 𝔼 vm vb) → point va == point vb
  graphPath va vb vm dom cod = lemma va vb vm (λ we → point (fst we)) dom cod (cell vm) where
    lemma : (va vb vm : 𝕍) (f : (Σ 𝕍 (𝔼 vm)) → X) (dom : 𝔼 vm va) (cod : 𝔼 vm vb) → ==i (point vm) f → f (va , dom) == f (vb , cod)
    lemma va vb vm f dom cod refli = idp
open FixModel public
