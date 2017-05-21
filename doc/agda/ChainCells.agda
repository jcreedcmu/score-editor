module ChainCells (A : Set) where

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
open import Level hiding ( zero ) renaming (suc to lsuc)
open import Function

data Tern : Set where
 t+ : Tern
 t- : Tern
 t0 : Tern

record Chain : Set₁ where
  field
    ℂ : ℕ → Set
    δ : (n : ℕ) → ℂ (suc n) → ℂ n → Tern

Good : Chain → Set
Good c = {!!}
