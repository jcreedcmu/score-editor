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

fulls : Set
fulls = hetVec (Data.Vec.map (λ _ → Bool) (comps ct))

cells : Set
cells = hetVec (Data.Vec.map Maybe (comps ct))

B = hetList (leaves ct)
C = B × cells
G = B × fulls

g-lemma : B → fulls -> hetVec (Data.Vec.map (λ A → Bool × A) (comps ct))
g-lemma b fs = zip-lemma (comps ct) (hetZip fs (compValues ct b))

g : G → C
g (b , fs) = (b , hetMapg (λ A → Bool × A) Maybe
                   (λ _ p → if proj₁ p then just (proj₂ p) else nothing)
                   (comps ct) (g-lemma b fs))

ρ : C → G
ρ (b , cache) = (b , hetMapg Maybe (λ _ → Bool) (λ _ mab -> is-just mab) (comps ct) cache)

ι : B → C
ι b = (b , hetMap Maybe (λ compTp -> nothing) (comps ct))

π : C → B
π (b , cache) = b

tree : Cache
tree = MkCache G C B g ρ ι π
