{-

This file uses agda-stdlib
The following should suffice to wire it up:

cd ~/.agda
git clone https://github.com/agda/agda-stdlib/
cd agda-stdlib
git co e25c3220f1d6cb8
cd ..
echo standard-library >> defaults
echo `pwd`/agda-stdlib/standard-library.agda-lib >> libraries

-}

module CacheTypes where

open import Data.Product
open import Data.Bool
open import Data.Maybe
open import Function
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
postulate
  funext : {A B : Set} {f g : A → B} → ((x : A) → f x ≡ g x) → f ≡ g

record Observable : Set1 where
  constructor MkObservable
  field
    B D : Set
    der : B → D

record Cache : Set1 where
  constructor MkCache
  field
    G C B : Set
    g : G → C
    ρ : C → G
    ι : B → C
    π : C → B

module GoodCache where
  open Cache
  record GoodCache (c : Cache) : Set where
    constructor MkGoodCache
    field
      gρ : (ρ c ∘ g c) ≡ id
      πι : (π c ∘ ι c) ≡ id
open GoodCache using (MkGoodCache ; GoodCache)

ex1 : Observable → Cache
ex1 o = MkCache B B B id id id id
  where
    open Observable renaming (B to oB)
    B = oB o

ex2 : Observable → Cache
ex2 o = MkCache G C B g ρ ι π
  where
    open Observable renaming (B to oB)
    B = oB o
    d = der o
    G = B × Bool
    C = B × Maybe (D o)

    g : G → C
    g (b , full) = (b , (if full then just (d b) else nothing))

    ρ : C → G
    ρ (b , cache) = (b , (maybe (λ _ → true) false cache))

    ι : B → C
    ι b = (b , nothing)

    π : C → B
    π (b , _) = b

ex2good : (o : Observable) → GoodCache (ex2 o)
ex2good o = MkGoodCache gρ πι where
  open Observable renaming (B to oB)
  open Cache using (g; ρ; π; ι)

  c = ex2 o
  B = oB o

  gρ-lemma : (y : B × Bool) -> (ρ c) ((g c) y) ≡ y
  gρ-lemma (y , true) = refl
  gρ-lemma (y , false) = refl

  πι-lemma : (y : B) -> (π c) ((ι c) y) ≡ y
  πι-lemma y = refl

  gρ : ρ c ∘ g c ≡ id
  gρ = funext gρ-lemma
  πι = funext πι-lemma
