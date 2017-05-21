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

record Bundle (n : ℕ) : Set₁ where
  constructor MkBundle
  field
    ℂ : PreCell n → Module
    𝔾 : Module
    ∂ : (c : PreCell n) → ModHom (ℂ c) 𝔾

IncBundle : {n : ℕ} → Bundle n → Bundle (suc n)
IncBundle {n} (MkBundle ℂ 𝔾 ∂) = MkBundle ℂ1 𝔾1 ∂1
  where
  𝔾1 : Module
  𝔾1 = ProductMod (PreCell n) ℂ
  G∂ : ModHom 𝔾1 𝔾
  G∂ = SumOver (PreCell n) ℂ 𝔾 ∂
  LocalSubM : (c : PreCell (suc n)) → ModHom (ResMod (PreCell n) ℂ c) 𝔾1
  LocalSubM c = ResSubMod (PreCell n) ℂ c
  ℂ1 : PreCell (suc n) → Module
  ℂ1 c = ker (ModHomComp (LocalSubM c) G∂)
  ∂1 : (c : PreCell (suc n)) → ModHom (ℂ1 c) 𝔾1
  ∂1 c = ModHomComp
    (KerHom (ModHomComp (ResSubMod (PreCell n) ℂ c) G∂))
    (LocalSubM c)

GiveBundle : (n : ℕ) → Bundle n
GiveBundle zero = MkBundle (λ _ → ℤMod) ℤMod (λ _ → IdHom ℤMod)
GiveBundle (suc n) = IncBundle (GiveBundle n)
