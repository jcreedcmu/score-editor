module IntCells (A : Set) where

-- open import Level renaming (suc to lsuc) hiding (zero)
open import Data.Integer renaming (suc to isuc ; _+_ to _i+_ ; _*_ to _i*_ ) hiding ( _⊔_ )
open import Data.Nat hiding ( _⊔_ )
open import Data.Unit
open import Data.Empty
open import Data.Bool
open import Data.Sum
open import Data.Product
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Level hiding ( zero )
open import Function

record _st_{a b} (A : Set a) (B : A → Set b) : Set (a ⊔ b) where
  constructor _,,_
  field
    Item : A
    .Pf : B Item -- proof irrelevance
open _st_

record Module : Set₁ where
  field
    X : Set
    m0 : X
    _++_ : X → X → X
    _**_ : ℤ → X → X

record _⇒_ (M N : Module) : Set where
  field
    f : (Module.X M) → (Module.X N)
    p1 : f (Module.m0 M) ≡ Module.m0 N


IdHom : (M : Module) → M ⇒ M
IdHom M = record { f = λ x → x ; p1 = refl }

ker : {M N : Module} → M ⇒ N → Module
ker {M} {N} hom = record {
  X = Σ (Module.X M) (λ m → (_⇒_.f hom m ≡ Module.m0 N)) ;
  m0 = (Module.m0 M) , (_⇒_.p1 hom) ;
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

restrict : (B : Set) (pred : B → Bool) → Set
restrict B pred = Σ B (λ b → pred b ≡ true)

{- a product module, but only over a boolean restriction of the index set -}
ResMod : (B : Set) (Mb : B → Module) (pred : B → Bool) → Module
ResMod B Mb pred = ProductMod (restrict B pred) (λ br → Mb (proj₁ br))

postulate
  {- this is meant to just be the inclusion -}
  ResSubMod : (B : Set) (Mb : B → Module) (pred : B → Bool) → (ResMod B Mb pred) ⇒ (ProductMod B Mb)
  {- this is also just the fact that the kernel, as an inclusion, is a homomorphism -}
  KerHom : {M N : Module} (f : M ⇒ N) → ker f ⇒ M

  _⊚_ : {M N P : Module} → M ⇒ N → N ⇒ P → M ⇒ P
  SumOver : (B : Set) (Mb : B → Module) (M : Module) → ((b : B) → Mb b ⇒ M)
            → ProductMod B Mb ⇒ M

  1Dim : Module → Set

record Bundle : Set₁ where
  constructor MkBundle
  field
    𝔾 : Module
    ℂ : Set
    𝕄 : ℂ → Module
    ∂ : (c : ℂ) → 𝕄 c ⇒ 𝔾

IncBundle : Bundle → Bundle
IncBundle (MkBundle 𝔾 ℂ 𝕄 ∂) =
  MkBundle (ProductMod ℂ 𝕄) ((ℂ → Bool) st (1Dim ∘ 𝕄')) (𝕄' ∘ Item) ((λ c → KerHom (LocGlo c) ⊚ (Local c)) ∘ Item)
  where
  Local = ResSubMod ℂ 𝕄
  LocGlo = λ c → Local c ⊚ (SumOver ℂ 𝕄 𝔾 ∂)
  𝕄' = ker ∘ LocGlo

GiveBundle : ℕ → Bundle
GiveBundle zero = MkBundle ℤMod A (λ _ → ℤMod) (λ _ → IdHom ℤMod)
GiveBundle (suc n) = IncBundle (GiveBundle n)
