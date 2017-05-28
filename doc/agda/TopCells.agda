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


  data ModelUpto : (n : ℕ) → Set
  data AllEq : (n : ℕ) (M : ModelUpto n) (s : 𝔻 𝕏 (suc n) → Set) → Set
  idModel : (x : X) (n : ℕ) → ModelUpto n

  data ModelUpto where
    mzero : ModelUpto 0
    msuc : {n : ℕ} (M : ModelUpto n) → ((c : 𝕏 n) → AllEq n M (δ (suc n) c)) →  ModelUpto (suc n)

  data AllEq where
    aeid : (x : X) (n : ℕ) (c : 𝕏 n) → AllEq n (idModel x n) (δ (suc n) c)

  idModel x 0 = mzero
  idModel x (suc n) = msuc (idModel x n) (aeid x n)





  -- Foo : Set
  -- Foo = (n : ℕ) (c : 𝕏 (suc n)) (g : 𝕏 n) (m : δ (suc (suc n)) c g) → {!!}
