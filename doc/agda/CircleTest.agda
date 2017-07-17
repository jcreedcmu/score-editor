{-# OPTIONS --without-K --rewriting #-}

open import HoTT hiding (Bool ; true ; false ; _$_ ; Path)

module CircleTest where

postulate
  ● : Set
  eqv : (X : Set) → (● → X) ≃ Σ X (λ x → x == x)

module _ where

  postulate  -- HIT
    ○ : Set

  module _ where

    postulate  -- HIT
      root : ○
      path : root == root

  module CircleElim {l} {P : ○ → Type l}
    (root* : P root)
    (path* : root* == root* [ P ↓ path ]) where

    postulate  -- HIT
      f : Π ○ P
      root-β : f root ↦ root*
    {-# REWRITE root-β #-}

    postulate  -- HIT
      path-β : apd f path == path*

○-elim = CircleElim.f

poℓ : ∀ {n} {X : Set} {P : Set n} {x1 x2 : X} {p1 p2 : P} (xℓ : x1 == x2) (pℓ : p1 == p2) → PathOver (λ _ → P) xℓ p1 p2
poℓ idp pℓ = pℓ

○-elimnd : ∀ {n} {P : Set n} (root* : P) (path* : root* == root*) → ○ → P
○-elimnd {n} {P} root* path* c = ○-elim {n} {P = λ _ → P} root* (poℓ path path*) c

prep = –> (eqv ●) (idf _)
●root : ●
●root = fst prep
●path : ●root == ●root
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

thm : ∀ {n}(X : Set n) → (○ → X) ≃ Σ X (λ x → x == x)
thm X = equiv into out zig zag where
  into : (○ → X) → Σ X (λ x → x == x)
  into f = (f root) , (ap f path)

  out : Σ X (λ x → x == x) → (○ → X)
  out (x , ℓ) = ○-elimnd x ℓ

  zig : (b : Σ X (λ x → x == x)) → into (out b) == b
  zig (x , ℓ) = pair= idp ziglem where
    ziglem : ap (○-elim x (poℓ path ℓ)) path == ℓ
    ziglem = {!!}

  zag : (a : ○ → X) → out (into a) == a
  zag f = λ= zaglem where
    zaglem : (c : ○) → ○-elimnd (f root) (ap f path) c == f c
    zaglem = {!!}

Xroot : (X : ○ → Set) → Set
Xroot X = fst (–> (thm Set) X)

Xpath : (X : ○ → Set) → (Xroot X == Xroot X)
Xpath X = snd (–> (thm Set) X)

thmd : (X : ○ → Set) → Π ○ X ≃ Σ (Xroot X) (λ root* → root* == root* [ X ↓ path ])
thmd = {!!}

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
