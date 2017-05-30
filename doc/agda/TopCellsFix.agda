{-# OPTIONS --without-K --rewriting #-}

module TopCellsFix where

open import HoTT hiding ( _$_ ; north ; south ) renaming ( Type to _Type )

{--- general way of specifying HITs? ---}

record Graph : Set₁ where
  constructor MkGraph
  field
    𝕍 : Set
    𝔼 : 𝕍 → 𝕍 → Set

data Gr : Set → Set₁ where
  gnil : Gr ⊤
  gcons : (Lo Hi : Set) (∂ : Hi → Lo → Set) → Gr Lo → Gr Hi


module GFixX (X : Set) where
  Mod : {Hi : Set} → Gr Hi → Set
  Id : (x : X) {Hi : Set} (G : Gr Hi) → Mod G

  Mod gnil = ⊤
  Mod (gcons Lo Hi ∂ G') = {!!}
  Id x gnil = tt
  Id x (gcons Lo Hi ∂ G') = {!!}

record ⊙Set : Set₁ where
  constructor Mk⊙Set
  field
    car : Set
    pt : car
open ⊙Set

data ispt (A : ⊙Set) : (a : car A) → Set where
  prefl : ispt A (pt A)


module FixX (X : Set) where
  Mod0 : (C0 : Set) → Set
  Mod0 C0 = C0 → X

  ⊙0 : (C0 : Set) (x : X) → ⊙Set
  ⊙0 C0 x = Mk⊙Set (Mod0 C0) (λ _ → x)

  E0 : (z : X) (C0 : Set) (f : Mod0 C0) → Set
  E0 z C0 f  = ispt (⊙0 C0 z) f

  Mod1 : (C0 : Set) (C1 : Set) (δ : C1 → C0 → Set) → Set
  Mod1 C0 C1 δ =  Σ (Mod0 C0) (λ M0 → (c1 : C1) → Σ X (λ x → E0 x (Σ C0 (δ c1)) (M0 ∘ fst)))

  ⊙1 : (x : X) (C0 : Set) (C1 : Set) (δ : C1 → C0 → Set) → ⊙Set
  ⊙1 x C0 C1 δ = Mk⊙Set (Mod1 C0 C1 δ) (pt (⊙0 C0 x) , (λ _ → x , prefl))

  E1 : (x : X) (C0 C1 : Set) (δ0 : C1 → C0 → Set) (f : Mod1 C0 C1 δ0) → Set
  E1 x C0 C1 δ0 f = ispt (⊙1 x C0 C1 δ0) f

  restrict0 : (C0 : Set) (C0' : C0 → Set)
    → Mod0 C0
    → Mod0 (Σ C0 C0')
  restrict0 C0 C0' M0 = M0 ∘ fst

  restrict1 : (C0 C1 : Set) (δ0 : C1 → C0 → Set) (C0' : C0 → Set) (C1' : C1 → Set)
    → Mod1 C0 C1 δ0
    → Mod1 (Σ C0 C0') (Σ C1 C1') (λ c1 c0 → δ0 (fst c1) (fst c0))
  restrict1 C0 C1 δ0 C0' C1' M1 = (restrict0 C0 C0' (fst M1)) , {!!}

  Mod2 : (C0 C1 C2 : Set) (δ0 : C1 → C0 → Set) (δ1 : C2 → C1 → Set) → Set
  Mod2 C0 C1 C2 δ0 δ1 = Σ (Mod1 C0 C1 δ0) (λ M1 → (c2 : C2) → modcond M1 c2)
    where
    modcond : Mod1 C0 C1 δ0 → C2 → Set
    modcond M1 c2 = Σ X (λ x → E1 x S0 S1 δ0' (restrict1 C0 C1 δ0 C0' C1' M1))
      where
      C0' = (λ c0 → Σ C1 (λ c1 → δ1 c2 c1 × δ0 c1 c0))
      C1' = δ1 c2
      S0 = Σ C0 C0'
      S1 = Σ C1 C1'
      δ0' : S1 → S0 → Set
      δ0' c1 c0 = δ0 (fst c1) (fst c0)




  -- check : (z : X) (C0 : Set) (c01 c02 : C0) (f : C0 → X) → E0 z C0 f → f c01 == f c02
  -- check z C0 c01 c02 .(λ _ → z) prefl = idp

  -- check2 : (z x y : X) → E0 z Bool (λ b → if b then x else y) → x == y
  -- check2 z x y p = check z Bool true false (λ b → if b then x else y) p

--  eqmorphs : (z : X) (C0 : Set) (C1 : Set) (bd : C1 → C0 → Set) (f0 : C0 → X) (f1
-- data ==i {A : Set} {B : Set} : B → (f : A → B) → Set where
--   refli : {b : B} → ==i b (λ _ → b)
-- -- (==i b (λ a → f a) means "b and all the f a are simultaneously equal")

-- module FixGraph (χ : Graph) (X : Set) where
--   open Graph χ

--   record Model : Set where
--     field
--       point : 𝕍 → X
--       cell : (v : 𝕍) → ==i (point v) (λ (we : Σ 𝕍 (𝔼 v)) → point (fst we))
-- open FixGraph
-- open FixGraph public using ( Model )

-- {--- define the circle via some cells ---}

-- data ○vert : Set where
--   vn vs ve vw : ○vert

-- data ○edge : ○vert → ○vert → Set where
--   enw : ○edge vw vn
--   esw : ○edge vw vs
--   ene : ○edge ve vn
--   ese : ○edge ve vs

-- ○gr : Graph
-- ○gr = MkGraph ○vert ○edge

-- {--- define the circle in a way that is hopefully convenient ---}

-- module _ where

--   postulate  -- HIT
--     ○ : Set

--   module _ where

--     postulate  -- HIT
--       north south : ○
--       east west : north == south

--   module ○Elim {P : ○ → Set}
--     (n* : P north)
--     (s* : P south)
--     (e* : n* == s*  [ P ↓ east ])
--     (w* : n* == s*  [ P ↓ west ]) where

--     postulate  -- HIT
--       f : Π (○) P
--       n-β : f north ↦ n*
--       s-β : f south ↦ s*
--     {-# REWRITE n-β #-}
--     {-# REWRITE s-β #-}

--     postulate -- HIT
--       e-β : apd f east ↦ e*
--       w-β : apd f west ↦ w*
--     {-# REWRITE e-β #-}
--     {-# REWRITE w-β #-}

-- ○-elim = ○Elim.f

-- {--- some lemmas ---}

-- pathToOver : {A X : Set} {a b : A} {x y : X} (p : a == b) → x == y → x == y [ (λ _ → X) ↓ p ]
-- pathToOver idp idp = idp

-- pointOfPath : {A : Set} {a b : A} → a == b → A
-- pointOfPath {A} {a} {.a} idp = a

-- pointOfPathDom : {A : Set} {a b : A} (p : a == b) → pointOfPath p == a
-- pointOfPathDom {A} {a} {.a} idp = idp

-- pointOfPathCod : {A : Set} {a b : A} (p : a == b) → pointOfPath p == b
-- pointOfPathCod {A} {a} {.a} idp = idp

-- api : {A B C : Set} {b : B} {k : A → B} (f : B → C) → ==i b k → ==i (f b) (f ∘ k)
-- api f refli = refli

-- module _Model= {χ : Graph} {X : Set}  where
--   open Graph χ
--   open Model
--   Model= : {M1 M2 : Model χ X}
--     (p : point M1 == point M2)
--     (q : cell M1 == cell M2 [ (λ π → (v : 𝕍) → ==i (π v) (λ (we : Σ 𝕍 (𝔼 v)) → π (fst we))) ↓ p ])
--     → M1 == M2
--   Model= idp idp = idp
-- open _Model= public

-- module FixModel {χ : Graph} {X : Set} (M : Model χ X) where
--   open Graph χ
--   open Model M

--   domPath : (va vm : 𝕍) (dom : 𝔼 vm va) → point va == point vm
--   domPath va vm dom = lemma va vm (λ we → point (fst we)) dom (cell vm) where
--     lemma : (va vm : 𝕍) (f : (Σ 𝕍 (𝔼 vm)) → X) (dom : 𝔼 vm va) → ==i (point vm) f → f (va , dom) == point vm
--     lemma va vm f dom refli = idp

--   graphPath : (va vb vm : 𝕍) (dom : 𝔼 vm va) (cod : 𝔼 vm vb) → point va == point vb
--   graphPath va vb vm dom cod = lemma va vb vm (λ we → point (fst we)) dom cod (cell vm) where
--     lemma : (va vb vm : 𝕍) (f : (Σ 𝕍 (𝔼 vm)) → X) (dom : 𝔼 vm va) (cod : 𝔼 vm vb) → ==i (point vm) f → f (va , dom) == f (vb , cod)
--     lemma va vb vm f dom cod refli = idp
-- open FixModel public
