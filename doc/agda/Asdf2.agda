{-# OPTIONS --without-K --rewriting #-}

module Asdf2 where

open import HoTT

postulate
  _~>_ : ∀ {n} {A : Set n} → A → A → Set
  refl~ : ∀ {n} {A : Set n} (a : A) → a ~> a
  comp~ : ∀ {n} {A : Set n} {a b c : A} → a ~> b → b ~> c → a ~> c

  comprefl~ : ∀ {n} {A : Set n} {x : A} → refl~ x == comp~ (refl~ x) (refl~ x)

data 𝟚 : Set where
  𝟘 𝟙 : 𝟚

X : Set
X = List 𝟚


record Stage : Set₁ where
  constructor MkStage
  field
    A : Set
    C D : A

record _=~_ {A : Set} (C D : A) : Set₁ where
  constructor Mk=~
  field
    tree : (bs : List 𝟚) → Stage
    f : (bs : List 𝟚) → Stage.C (tree bs) ~> Stage.D (tree bs)
    g : (bs : List 𝟚) → Stage.D (tree bs) ~> Stage.C (tree bs)
    treeε : tree nil == MkStage A C D
    tree0 : (bs : List 𝟚) → tree (𝟘 :: bs) == MkStage (Stage.C (tree bs) ~> Stage.C (tree bs)) (refl~ (Stage.C (tree bs))) (comp~ (f bs) (g bs))
    tree1 : (bs : List 𝟚) → tree (𝟙 :: bs) == MkStage (Stage.D (tree bs) ~> Stage.D (tree bs)) (refl~ (Stage.D (tree bs))) (comp~ (g bs) (f bs))


thm : {A : Set} (x : A) → x =~ x
thm {A} x = Mk=~ tree f g idp tree0 tree1 where
  tree : (bs : List 𝟚) → Stage
  tree nil = MkStage A x x
  tree (_ :: bs) = MkStage (pC ~> pC) (refl~ pC) (refl~ pC) where
    open Stage (tree bs) renaming (A to pA ; C to pC ; D to pD)
  f : (bs : List 𝟚) → Stage.C (tree bs) ~> Stage.D (tree bs)
  f nil = refl~ x
  f (b :: bs) = refl~ (refl~ (Stage.C (tree bs)))
  g : (bs : List 𝟚) → Stage.D (tree bs) ~> Stage.C (tree bs)
  g nil = refl~ x
  g (b :: bs) = refl~ (refl~ (Stage.C (tree bs)))
  eq1 : (bs : List 𝟚) → refl~ (Stage.C (tree bs)) == comp~ (f bs) (g bs)
  eq1 nil = comprefl~
  eq1 (b :: bs) = comprefl~
  eq2 : (bs : List 𝟚) → refl~ (Stage.D (tree bs)) == comp~ (g bs) (f bs)
  eq2 nil = comprefl~
  eq2 (b :: bs) = comprefl~
  eq3 : (bs : List 𝟚) →
      MkStage (Stage.C (tree bs) ~> Stage.C (tree bs))
      (refl~ (Stage.C (tree bs))) (refl~ (Stage.C (tree bs)))
        ==
      MkStage (Stage.D (tree bs) ~> Stage.D (tree bs))
      (refl~ (Stage.D (tree bs))) (refl~ (Stage.D (tree bs)))
  eq3 nil = idp
  eq3 (_ :: _) = idp
  tree0 : (bs : List 𝟚) →
      MkStage (Stage.C (tree bs) ~> Stage.C (tree bs))
      (refl~ (Stage.C (tree bs))) (refl~ (Stage.C (tree bs)))
      ==
      MkStage (Stage.C (tree bs) ~> Stage.C (tree bs))
      (refl~ (Stage.C (tree bs))) (comp~ (f bs) (g bs))
  tree0 bs = ap (MkStage (Stage.C (tree bs) ~> Stage.C (tree bs)) (refl~ (Stage.C (tree bs)))) (eq1 bs)
  tree1 : (bs : List 𝟚) →
      MkStage (Stage.C (tree bs) ~> Stage.C (tree bs))
      (refl~ (Stage.C (tree bs))) (refl~ (Stage.C (tree bs)))
      ==
      MkStage (Stage.D (tree bs) ~> Stage.D (tree bs))
      (refl~ (Stage.D (tree bs))) (comp~ (g bs) (f bs))
  tree1 bs = eq3 bs ∙ ap (MkStage (Stage.D (tree bs) ~> Stage.D (tree bs)) (refl~ (Stage.D (tree bs)))) (eq2 bs)

postulate

  converse : ∀ {n} {A : Set n} (C D : A) (f : C ~> D) (g : D ~> C)
    (zig : comp~ f g == refl~ C)
    (zag : comp~ g f == refl~ D)
    → C == D
