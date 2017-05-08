module IntCells (A : Set) where

-- open import Level renaming (suc to lsuc) hiding (zero)
open import Data.Integer renaming (suc to isuc ; _+_ to _i+_ ; _*_ to _i*_ )
open import Data.Nat
open import Data.Unit
open import Data.Empty
open import Data.Bool
open import Data.Sum
open import Data.Product
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

Space : Set → Set
Space A = A → ℤ

record Module : Set₁ where
  field
    X : Set
    m0 : X
    _++_ : X → X → X
    _**_ : ℤ → X → X

record ModHom (M N : Module) : Set where
  field
    f : (Module.X M) → (Module.X N)
    p1 : f (Module.m0 M) ≡ Module.m0 N

IdHom : (M : Module) → ModHom M M
IdHom M = record { f = λ x → x ; p1 = refl }

ker : {M N : Module} → ModHom M N → Module
ker {M} {N} hom = record {
  X = Σ (Module.X M) (λ m → (ModHom.f hom m ≡ Module.m0 N)) ;
  m0 = (Module.m0 M) , (ModHom.p1 hom) ;
  _++_ = λ k1 k2 → (Module._++_ M (proj₁ k1) (proj₁ k2)) , {!!} ;
  _**_ = {!!} }

{- I'm confident the above can be constructed, just too bored to do it right now -}

ℤMod : Module
ℤMod = record {
  X = ℤ ;
  m0 = + zero ;
  _++_ = λ z1 z2 → z1 i+ z2 ;
  _**_ = λ z1 z2 → z1 i* z2  }

FreeMod : Set → Module
FreeMod A = record {
  X = A → ℤ ;
  m0 = λ a → + zero ;
  _++_ = λ m1 m2 a → m1 a i+ m2 a ;
  _**_ = λ z m a → z i* m a  }

{- product together a B-indexed family of modules -}
ProductMod : (B : Set) → (B → Module) → Module
ProductMod B f = record {
  X = (b : B) → Module.X (f b) ;
  m0 = λ b → Module.m0 (f b) ;
  _++_ = λ x y b →  Module._++_ (f b) (x b) (y b) ;
  _**_ = λ z x b → Module._**_ (f b) z (x b)  }

PreCell : ℕ → Set
PreCell zero = A
PreCell (suc n) = PreCell n → Bool

restrict : (B : Set) (pred : B → Bool) → Set
restrict B pred = Σ B (λ b → pred b ≡ true)

{- a product module, but only over a boolean restriction of the index set -}
ResMod : (B : Set) (Mb : B → Module) (pred : B → Bool) → Module
ResMod B Mb pred = ProductMod (restrict B pred) (λ br → Mb (proj₁ br))

postulate
  {- this is meant to just be the inclusion -}
  ResSubMod : (B : Set) (Mb : B → Module) (pred : B → Bool) → ModHom (ResMod B Mb pred) (ProductMod B Mb)
  {- this is also just the fact that the kernel, as an inclusion, is a homomorphism -}
  KerHom : {M N : Module} (f : ModHom M N) → ModHom (ker f) M

  ModHomComp : {M N P : Module} → ModHom M N → ModHom N P → ModHom M P
  SumOver : (B : Set) (Mb : B → Module) (M : Module) → ((b : B) → ModHom (Mb b) M)
            → ModHom (ProductMod B Mb) M

CellModule : (n : ℕ) → PreCell n → Module
GlobalModule : (n : ℕ) → Module
CellBoundary : (n : ℕ) (c : PreCell n) → ModHom (CellModule n c) (GlobalModule n)
GlobalBoundary : (n : ℕ) → ModHom (GlobalModule (suc n)) (GlobalModule n)
LocalSubMod : (n : ℕ) (c : PreCell (suc n)) → ModHom (ResMod (PreCell n) (CellModule n) c) (GlobalModule (suc n))

GlobalModule zero = ℤMod
GlobalModule (suc n) = ProductMod (PreCell n) (CellModule n)
LocalSubMod n c = ResSubMod (PreCell n) (CellModule n) c

GlobalBoundary n = SumOver (PreCell n) (CellModule n) (GlobalModule n) (λ b → CellBoundary n b)
CellModule zero a = ℤMod
CellModule (suc n) c =
  ker (ModHomComp (LocalSubMod n c) (GlobalBoundary n))
CellBoundary zero c = IdHom ℤMod
CellBoundary (suc n) c =
  ModHomComp
    (KerHom (ModHomComp (ResSubMod (PreCell n) (CellModule n) c) (GlobalBoundary n)))
    (LocalSubMod n c)


{--

A 3-cell is given by a mapping f from 2-cells to bool. The elements
of its module are the kernel of the boundary map from the support of f.

The boundary map from a 3-cell is a map from its module to the product module
over the modules of all 2-cells given by taking
--}
