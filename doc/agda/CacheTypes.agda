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
    d : B → D

record Cache : Set1 where
  constructor MkCache
  field
    G C B : Set
    g : G → C
    ρ : C → G
    ι : B → C
    π : C → B

private
  module GoodCache where
    open Cache
    record GoodCache (c : Cache) : Set where
      constructor MkGoodCache
      field
        gρ : (ρ c ∘ g c) ≡ id
        πι : (π c ∘ ι c) ≡ id
open GoodCache public using (MkGoodCache ; GoodCache)

module CacheMorphism where
  open Cache
  record CacheMorphism (t1 t2 : Cache) : Set where
    constructor MkCacheMorphism
    field
      f : C t1 → C t2
      fgρ : g t2 ∘ ρ t2 ∘ f ∘ g t1 ≡ f ∘ g t1
      fπι : π t2 ∘ f ∘ ι t1 ∘ π t1 ≡ π t2 ∘ f
