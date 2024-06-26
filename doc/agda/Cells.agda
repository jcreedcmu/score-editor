module Cells (A : Set) where

open import Data.Nat
open import Data.Unit
open import Data.Empty
open import Data.Bool
open import Data.Sum
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

data Tern : Set where
 t+ : Tern
 t- : Tern
 t0 : Tern

_**_ : Tern -> Tern -> Tern
t0 ** _ = t0
_ ** t0 = t0
t+ ** x = x
x ** t+ = x
t- ** t- = t+

PreCells : Set₁
PreCells = ℕ → Set

getPred : (pc : PreCells) (n : ℕ) → Set
getPred pc zero = ⊤
getPred pc (suc n) = pc n

record Cells : Set₁ where
  field
    pc : PreCells
    funcs : {n : ℕ} -> pc n → getPred pc n → Tern


module GoodAt (n : ℕ) (c : Cells) where
  pc = Cells.pc c
  predt = getPred pc n
  midt = pc n
  suct = pc (suc n)
  _#_ : {n : ℕ} -> pc n → getPred pc n → Tern
  x # y = Cells.funcs c x y

  record goodPair (f : suct) (x : predt) : Set where
    field
      m+ m- : midt
      p+ : (f # m+) ** (m+ # x) ≡ t+
      p- : (f # m-) ** (m- # x) ≡ t-
      fz : (m : midt) -> m ≡ m+ ⊎ m ≡ m- ⊎ (f # m) ** (m # x) ≡ t0

  good : Set
  good = (f : suct) (x : predt) -> goodPair f x ⊎ ((m : midt) → (f # m) ** (m # x) ≡ t0)
