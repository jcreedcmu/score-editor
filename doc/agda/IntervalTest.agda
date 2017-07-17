{-# OPTIONS --without-K --rewriting #-}

open import HoTT hiding (Bool ; true ; false ; _$_ ; Path)

module IntervalTest where

postulate
  ● : Set
  eqv : (X : Set) → (● → X) ≃ Σ (X × X) (λ xy → fst xy == snd xy)

module _ where

  postulate  -- HIT
    ○ : Set

  module _ where

    postulate  -- HIT
      ia ib : ○
      path : ia == ib

  module IntervalElim {l} {P : ○ → Type l}
    (a* : P ia)
    (b* : P ib)
    (path* : a* == b* [ P ↓ path ]) where

    postulate  -- HIT
      f : Π ○ P
      a-β : f ia ↦ a*
      b-β : f ib ↦ b*
    {-# REWRITE a-β #-}
    {-# REWRITE b-β #-}

    postulate  -- HIT
      path-β : apd f path == path*

○-elim = IntervalElim.f

poℓ : ∀ {n} {X : Set} {P : Set n} {x1 x2 : X} {p1 p2 : P} (xℓ : x1 == x2) (pℓ : p1 == p2) → PathOver (λ _ → P) xℓ p1 p2
poℓ idp pℓ = pℓ

○-elimnd : ∀ {n} {P : Set n} (a* b* : P) (path* : a* == b*) → ○ → P
○-elimnd {n} {P} a* b* path* c = ○-elim {n} {P = λ _ → P} a* b* (poℓ path path*) c

prep = –> (eqv ●) (idf _)
●a : ●
●a = fst (fst prep)
●b : ●
●b = snd (fst prep)
●path : ●a == ●b
●path = snd prep


{-
thm : ● ≃ ○
thm = equiv into out zig zag where
  into : ● → ○
  into = <– (eqv ○) (root , path)

  out : ○ → ●
  out = ○-elimnd {P = ●} ●root ●path

  zig : (b : ○) → into (out b) == b
  zig = ○-elim {P = λ b → into (out b) == b} root* path* where
    -- root* : into (out root) == root
    root* : <– (eqv ○) (root , path) (○-elimnd {P = ●} ●root ●path root) == root
    root* = {!!}
    path* : root* == root* [ (λ b → into (out b) == b) ↓ path ]
    path* = {!!}
  zag = {!!}
-}

thm : ∀ {n}(X : Set n) → (○ → X) ≃ Σ (X × X) (λ xy → fst xy == snd xy)
thm X = equiv into out zig zag where
  into : (○ → X) → Σ (X × X) (λ xy → fst xy == snd xy)
  into f = (f ia , f ib) , (ap f path)

  out : Σ (X × X) (λ xy → fst xy == snd xy) → (○ → X)
  out ((x , y) , ℓ) = ○-elimnd x y ℓ

  zig : (b : Σ (X × X) (λ xy → fst xy == snd xy)) → into (out b) == b
  zig ((x , y) , ℓ) = pair= idp ziglem where
    ziglem : ap (○-elim x y (poℓ path ℓ)) path == ℓ
    ziglem = {!!}

  zag : (a : ○ → X) → out (into a) == a
  zag f = λ= zaglem where
    zaglem : (c : ○) → ○-elimnd (f ia) (f ib) (ap f path) c == f c
    zaglem = {!!}


Xa : (X : ○ → Set) → Set
Xa X = fst (fst (–> (thm Set) X))

Xb : (X : ○ → Set) → Set
Xb X = snd (fst (–> (thm Set) X))

Xpath : (X : ○ → Set) → (Xa X == Xb X)
Xpath X = snd (–> (thm Set) X)

holdsAcross : {A B : Set} → (A × B) → A == B → Set
holdsAcross (a , b) idp = a == b

Holds : Σ (Set × Set) (λ xy → fst xy == snd xy) → Set
Holds ((A , B) , e) = Σ (A × B) (λ ab → holdsAcross ab e) where

halem : {C : Set} {X : C → Set} (f : Π C X) (x y : C) (path : x == y) → holdsAcross (f x , f y) (ap X path)
halem f x y idp = idp

halem2 : {C : Set} {X : C → Set} {ca cb : C} {aa : X ca} {bb : X cb} (path : ca == cb) → holdsAcross (aa , bb) (ap X path) → PathOver X path aa bb
halem2 idp z = z

thmd : (X : ○ → Set) → Π ○ X ≃ Holds (–> (thm Set) X)
thmd X = equiv into out zig zag where
  into : Π ○ X → Holds (–> (thm Set) X)
  into f = ((f ia) , (f ib)) , halem f ia ib path
  out : Holds (–> (thm Set) X) → Π ○ X
  out ((aa , bb) , pp) = ○-elim {P = X} aa bb (halem2 path pp)
  zig = {!!}
  zag = {!!}

⊥UnivProp : (⊥ : Set) → Set₁
⊥UnivProp ⊥ = (X : Set) → (⊥ → X) ≃ ⊤

lem : {Z C : Set} → Z == ⊤ → (f1 f2 : Z) (a : Z → C) → a f1 == a f2
lem idp f1 f2 a = idp

lem2 : {A B : Set} → (A → B) ≃ ⊤ → (f1 f2 : A → B) (a : A) → f1 a == f2 a
lem2 {A} {B} e f1 f2 a = lem {A → B} {B} (ua e) f1 f2 (λ f → f a)

⊥UnivThm : (A1 A2 : Set) → ⊥UnivProp A1 → ⊥UnivProp A2 → A1 ≃ A2
⊥UnivThm A1 A2 u1 u2 = equiv (<– (u1 A2) tt) (<– (u2 A1) tt) zig zag where
  zig : (b : A2) → <– (u1 A2) unit (<– (u2 A1) unit b) == b
  zig b = lem2 (u2 A2) (λ b → <– (u1 A2) unit (<– (u2 A1) unit b)) (idf A2) b
  zag : (b : A1) → <– (u2 A1) unit (<– (u1 A2) unit b) == b
  zag b = lem2 (u1 A1) (λ b → <– (u2 A1) unit (<– (u1 A2) unit b)) (idf A1) b

⊤UnivProp : (U : Set) → Set₁
⊤UnivProp U = (X : Set) → (U → X) ≃ X

⊤UnivProp2 : (U : Set) → Set₁
⊤UnivProp2 U = (X : Set) → (X → U) ≃ ⊤


⊤UnivThm : (A1 A2 : Set) → ⊤UnivProp2 A1 → ⊤UnivProp2 A2 → A1 ≃ A2
⊤UnivThm A1 A2 u1 u2 = equiv (<– (u2 A1) tt) (<– (u1 A2) tt) zig zag where
  zig : (b : A2) → <– (u2 A1) unit (<– (u1 A2) unit b) == b
  zig b = lem2 (u2 A2) (λ b → <– (u2 A1) unit (<– (u1 A2) unit b)) (idf A2) b
  zag : (b : A1) → <– (u1 A2) unit (<– (u2 A1) unit b) == b
  zag b = lem2 (u1 A1) (λ b → <– (u1 A2) unit (<– (u2 A1) unit b)) (idf A1) b

&UnivProp2 : (U : Set) (A B : Set) (π1 : U → A) (π2 : U → B) → Set₁
&UnivProp2 U A B π1 π2 = (X : Set) (x1 : X → A) (x2 : X → B) → Σ (X → U) (λ f → (π1 ∘ f == x1) × (π2 ∘ f == x2)) ≃ ⊤


{-
thm2 : (A B : Set) → ((X : Set) → (A → X) ≃ (B → X)) → A ≃ B
thm2 A B e = equiv (<– (e B) (idf _)) (–> (e A) (idf _)) {!!} {!!}

thm3 : (A B : Set) → ((X : Set) → X ≃ (B → X)) → ⊤ ≃ B
thm3 A B e = equiv (λ tt → <– (e B) (idf _)) (λ _ → tt) lem (λ tt → idp) where
  lem2 : (b1 b2 : B) → b2 == –> (e B) b1 b2
  lem2 = {!!}

  lem : (b : B) → <– (e B) (idf B) == b
  lem b =  ap (<– (e B)) (λ= (λ b2 → lem2 b b2)) ∙ <–-inv-l (e B) b

parametric : {A B : Set} (f : (X : Set) → (A → X) → (B → X)) → Set₁
parametric {A} {B} f = (X Y : Set) (_R_ : X → Y → Set) (gx : A → X) (gy : A → Y) (gr : (a : A) → gx a R gy a) → (b : B) → f X gx b R f Y gy b

lemma : {A B : Set} (f : (X : Set) → (A → X) → (B → X)) → parametric f → (k : A → B) → (b : B) → k (f A (idf A) b) == f B k b
lemma {A} {B} f π k =  π A B (λ x y → k x == y) (idf A) k (λ a → idp)
-- hum2 : {X C D : Set} (f : ((X : Set) → (C → X) → X)) (k : D → X) (g : C → D) →
--    k (f D g) == f X (k ∘ g)
-- hum2 {X} {C} {D} f k g = param D X (λ x y → k x == y) C f g (k ∘ g) (λ c → idp)
-}
