open import CacheTypes


open import Data.Product
open import Data.Bool
open import Data.Maybe
open import Data.Nat
open import Data.Vec
open import Data.List
open import Function
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

module TreeExample {n : ℕ} (As : Vec Set n) (ct : CompTree As) where

B = hetList (leaves ct)
C = B × hetList (Data.List.map Maybe (comps ct))
G = B × hetList (Data.List.map (λ _ → Bool) (comps ct))

g : G → C
g = {!!}

ρ : C → G
ρ (b , cache) = (b , hetMapg Maybe (λ _ → Bool) (λ _ mab -> is-just mab) (comps ct) cache)

ι : B → C
ι b = (b , hetMap Maybe (λ compTp -> nothing) (comps ct))

π : C → B
π (b , cache) = b

tree : Cache
tree = MkCache G C B g ρ ι π
