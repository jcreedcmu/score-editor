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

hetVec : ∀ {a} {n : ℕ} -> Vec (Set a) n -> Set a
hetVec v = hetList (toList v)

hetMap : ∀ {a b} {n : ℕ} {A : Set a} -> (t : A -> Set b) (f : (x : A) → t x) (ℓ : Vec A n) -> hetVec (Data.Vec.map t ℓ)
hetMap t f [] = pnil
hetMap t f (x ∷ ℓ) =  pcons (f x) (hetMap t f ℓ)

hetMapDown : ∀ {a b} {A : Set a} -> (ℓ : List (Set b)) -> hetList (Data.List.map (λ _ → A) ℓ) -> List A
hetMapDown [] pnil = []
hetMapDown (x ∷ ℓ) (pcons y hℓ) = y ∷ hetMapDown ℓ hℓ

hetMapg : ∀ {a b} {n : ℕ} {A : Set a} -> (t u : A -> Set b) (f : (x : A) → t x → u x) (ℓ : Vec A n)
          -> hetVec (Data.Vec.map t ℓ) -> hetVec (Data.Vec.map u ℓ)
hetMapg t u f [] pnil = pnil
hetMapg t u f (x ∷ ℓ) (pcons px pℓ) =  pcons (f x px) (hetMapg t u f ℓ pℓ)

prodSubVec : {n : ℕ} -> Vec Set n -> FinSub n -> Set
prodSubVec v ss = hetList (filterVec v ss)


record Comp {n : ℕ} (As : Vec Set n) (A : Set) : Set where
  field
    deps : FinSub n
    comp : prodSubVec As deps -> A

data CompTree : {n : ℕ} (As : Vec Set n) -> Set1 where
  cnil : CompTree []
  cleaf : {n : ℕ} {As : Vec Set n} (A : Set) -> CompTree As -> CompTree (A ∷ As)
  ccomp : {n : ℕ} {As : Vec Set n} {A : Set} -> Comp As A -> CompTree As -> CompTree (A ∷ As)

leaves : {n : ℕ} {As : Vec Set n} -> CompTree As -> List Set
leaves cnil = []
leaves (cleaf A ct) = A ∷ leaves ct
leaves (ccomp _ ct) = leaves ct

numComps : {n : ℕ} {As : Vec Set n} -> CompTree As -> ℕ
numComps cnil = zero
numComps (cleaf _ ct) = numComps ct
numComps (ccomp _ ct) = suc (numComps ct)

comps : {n : ℕ} {As : Vec Set n} (ct : CompTree As) -> Vec Set (numComps ct)
comps cnil = []
comps (cleaf _ ct) = comps ct
comps (ccomp {A = A} _ ct) = A ∷ comps ct

sieve : {n : ℕ} (As : Vec Set n) (ss : FinSub n) -> hetVec As -> hetList (filterVec As ss)
sieve [] [] pnil = pnil
sieve (A ∷ As) (false ∷ As?) (pcons h tl) = sieve As As? tl
sieve (A ∷ As) (true ∷ As?) (pcons h tl) = pcons h (sieve As As? tl)

eval : {n : ℕ} {As : Vec Set n} {A : Set} -> Comp As A -> hetVec As -> A
eval f vs = Comp.comp f (sieve _ (Comp.deps f) vs)

values : {n : ℕ} {As : Vec Set n} (ct : CompTree As) -> hetList (leaves ct) -> hetVec As
values cnil lvs = pnil
values (cleaf x ct) (pcons lv lvs) = pcons lv (values ct lvs)
values (ccomp f ct) lvs = pcons (eval f (values ct lvs)) (values ct lvs)

zipProd : ∀ {a} {n : ℕ} (As Bs : Vec (Set a) n) -> Vec (Set a) n
zipProd {a} As Bs = Data.Vec.map (λ p → (proj₁ p) × (proj₂ p)) (Data.Vec.zip As Bs)


hetZip : ∀ {a} {n : ℕ} {As Bs : Vec (Set a) n} -> hetVec As -> hetVec Bs -> hetVec (zipProd As Bs)
hetZip {As = []} {[]} pnil pnil = pnil
hetZip {As = A ∷ As} {B ∷ Bs} (pcons a la) (pcons b lb) = pcons (a , b) (hetZip la lb)

compValues : {n : ℕ} {As : Vec Set n} (ct : CompTree As) -> hetList (leaves ct) -> hetVec (comps ct)
compValues ct lvs = compValues' ct (values ct lvs) where
  compValues' : {n : ℕ} {As : Vec Set n} (ct : CompTree As) -> hetVec As -> hetVec (comps ct)
  compValues' {zero} {[]} cnil pnil = pnil
  compValues' {suc n} {A ∷ As} (cleaf _ ct) (pcons _ values) = compValues' ct values
  compValues' {suc n} {A ∷ As} (ccomp f ct) (pcons v values) = pcons v (compValues' ct values)

-- here's where I could use univalence, I guess...
zip-lemma : {n : ℕ} (v : Vec Set n) →
        hetVec (zipProd (Data.Vec.map (λ _ → Bool) v) v) ->
        hetVec (Data.Vec.map (λ A → Bool × A) v)
zip-lemma [] pnil = pnil
zip-lemma (x ∷ v) (pcons y hv) = pcons y (zip-lemma v hv)
