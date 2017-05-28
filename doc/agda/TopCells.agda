module TopCells where

open import Level using (_⊔_)
open import Data.Nat hiding (_⊔_)
open import Data.Unit
open import Data.Product
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.Empty
open import Data.Sum renaming ( _⊎_ to _⊕_ )
open import BoolUtil using (_≅_ ; _st_ ; IsoFor ; MkIsoFor)
open _st_

open import FuncCells3 using ( Chain ; 𝔻 )

module FixChain (χ : Chain) (X : Set) where
  open Chain χ

  ModelUpto : (n : ℕ) → Set
  ModelAt : (n : ℕ) (M : ModelUpto n) → Set
  Cell : (n : ℕ) (M : ModelUpto n) (c : 𝕏 n) → Set
  Restrict : (n : ℕ) (M : ModelUpto n) (d : 𝕏 n) → {!δ (suc n) d!} -- Partial (suc n) M (δ (suc (suc n)) d)
  Partial0 : (M : ModelUpto 1) (s : 𝕏 0 → Set) → Set
  Partial : (n : ℕ) (M : ModelUpto n) (s : 𝕏 n → Set) → Set
  AllEq : (n : ℕ) (M : ModelUpto n) (s : 𝕏 n → Set) → Partial n M s → Set
  Restrict0 : (M : ModelUpto 1) (c : 𝕏 1) → Partial0 M (δ 2 c)

{----}

  ModelUpto 0 = ⊤
  ModelUpto (suc n) = Σ (ModelUpto n) (ModelAt n)

  Restrict0 = {!!}
  Partial0 M s = (c : 𝕏 0) (m : s c) → Cell 0 (proj₁ M) c

  ModelAt n M = (c : 𝕏 n) → Cell n M c

  Partial n M s = (c : 𝕏 n) (m : s c) → Cell n M c

  Restrict = {!!}
  AllEq = {!!}


  Cell zero M c = X
  Cell (suc zero) M c = {!AllEq0 M s (Restrict0 M c)!} -- AllEq n M' s (Restrict n M' c)
  Cell (suc (suc n)) M c = {!!} -- AllEq n M' s (Restrict n M' c)
    where
    M' = proj₁ M
    s = δ (suc (suc (suc n))) c



{---}

  -- Big fat mutual recursive definition here
  -- -- Declarations:
  -- data ModelUpto : (n : ℕ) → Set
  -- data AllEq : (n : ℕ) (M : ModelUpto n) (s : 𝔻 𝕏 (suc n) → Set) → Set
  -- idModel : (x : X) (n : ℕ) → ModelUpto n
  -- PartialModelUnder : (n : ℕ) (M : ModelUpTo n) (c : 𝕏 (suc n)) → Set

  -- -- Definitions:
  -- data ModelUpto where
  --   mzero : ModelUpto 0
  --   msuc : {n : ℕ} (M : ModelUpto n) → ((c : 𝕏 n) → AllEq n M (δ (suc n) c)) →  ModelUpto (suc n)

  -- data AllEq where
  --   aeid : (x : X) (n : ℕ) (c : 𝕏 n) → AllEq n (idModel x n) (δ (suc n) c)

  -- idModel x 0 = mzero
  -- idModel x (suc n) = msuc (idModel x n) (aeid x n)

  -- PartialModelUnder n M c = (g : 𝕏 n) (m : δ n c g) → AllEq n M





  -- Foo : Set
  -- Foo = (n : ℕ) (c : 𝕏 (suc n)) (g : 𝕏 n) (m : δ (suc (suc n)) c g) → {!!}
