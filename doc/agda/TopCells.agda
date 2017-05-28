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

{-- decls --}

  ModelUpto : (n : ℕ) → Set
  ModelAt : (n : ℕ) (M : ModelUpto n) → Set
  Cell : (n : ℕ) (M : ModelUpto n) (c : 𝕏 n) → Set
  Partial : (n : ℕ) (M : ModelUpto (suc n)) (d : 𝕏 (suc n)) → Set
  Restrict : (n : ℕ) (M : ModelUpto (suc n)) (d : 𝕏 (suc n)) → Partial n M d
  data AllEq (n : ℕ) : (M : ModelUpto (suc n)) (d : 𝕏 (suc n)) → Partial n M d → Set

  idModel : X → (n : ℕ) → ModelUpto n
  idCell : (x : X) → (n : ℕ) (c : 𝕏 n) → Cell n (idModel x n) c

{-- defns --}

  ModelUpto 0 = ⊤
  ModelUpto (suc n) = Σ (ModelUpto n) (ModelAt n)

  ModelAt n M = (c : 𝕏 n) → Cell n M c

  Partial n M d = (c : 𝕏 n) (m : δ (suc (suc n)) d c) → Cell n (proj₁ M) c

  Restrict n M d c m = proj₂ M c
  data AllEq (n : ℕ) where
    aeid : (x : X) (c : 𝕏 (suc n)) → AllEq n (idModel x (suc n)) c (Restrict n (idModel x (suc n)) c)

  Cell zero M c = X
  Cell (suc n) M c = AllEq n M c (Restrict n M c)

  idModel x zero = tt
  idModel x (suc n) = (idModel x n) , (idCell x n)

  idCell x zero c = x
  idCell x (suc n) c = aeid x c
