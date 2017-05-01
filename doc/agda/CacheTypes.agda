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

open Cache

record GoodCache (c : Cache) : Set where
  constructor MkGoodCache
  field
    gρ : (ρ c ∘ g c) ≡ id
    πι : (π c ∘ ι c) ≡ id

record CacheMorphism (t1 t2 : Cache) : Set where
  constructor MkCacheMorphism
  field
    f : C t1 → C t2
    fgρ : g t2 ∘ ρ t2 ∘ f ∘ g t1 ≡ f ∘ g t1
    fπι : π t2 ∘ f ∘ ι t1 ∘ π t1 ≡ π t2 ∘ f

open import Data.Vec
open import Data.List
open import Data.Nat
open import Data.Unit


FinSub : ℕ → Set
FinSub n = Vec Bool n

filterVec : ∀ {ℓ} {n : ℕ} {A : Set ℓ} -> Vec A n -> FinSub n -> List A
filterVec v ss = gfilter
  (λ x -> if proj₂ x then just (proj₁ x) else nothing)
  (toList (Data.Vec.zip v ss))

data hetList {a} : List (Set a) -> Set a where
  pnil : hetList []
  pcons : {A : Set a} {As : List (Set a)} -> A -> hetList As -> hetList (A ∷ As)

hetMap : ∀ {a b} {A : Set a} -> (t : A -> Set b) (f : (x : A) → t x) (ℓ : List A) -> hetList (Data.List.map t ℓ)
hetMap t f [] = pnil
hetMap t f (x ∷ ℓ) =  pcons (f x) (hetMap t f ℓ)

hetMapg : ∀ {a b} {A : Set a} -> (t u : A -> Set b) (f : (x : A) → t x → u x) (ℓ : List A)
          -> hetList (Data.List.map t ℓ) -> hetList (Data.List.map u ℓ)
hetMapg t u f [] pnil = pnil
hetMapg t u f (x ∷ ℓ) (pcons px pℓ) =  pcons (f x px) (hetMapg t u f ℓ pℓ)

prodSubVec : {n : ℕ} -> Vec Set n -> FinSub n -> Set
prodSubVec v ss = hetList (filterVec v ss)

prodVec : {n : ℕ} -> Vec Set n -> Set
prodVec v = hetList (toList v)

record Comp {n : ℕ} (As : Vec Set n) (A : Set) : Set where
  field
    deps : FinSub n
    comp : prodSubVec As deps -> A

data CompTree : {n : ℕ} (As : Vec Set n) -> Set1 where
  cnil : CompTree []
  cleaf : {n : ℕ} {As : Vec Set n} {A : Set} -> A -> CompTree As -> CompTree (A ∷ As)
  ccomp : {n : ℕ} {As : Vec Set n} {A : Set} -> Comp As A -> CompTree As -> CompTree (A ∷ As)

leaves : {n : ℕ} {As : Vec Set n} -> CompTree As -> List Set
leaves cnil = []
leaves (cleaf {A = A} _ ct) = A ∷ leaves ct
leaves (ccomp _ ct) = leaves ct

comps : {n : ℕ} {As : Vec Set n} -> CompTree As -> List Set
comps cnil = []
comps (cleaf _ ct) = comps ct
comps (ccomp {A = A} _ ct) = A ∷ comps ct
