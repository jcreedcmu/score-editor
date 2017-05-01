open import CacheTypes

open import Data.Product
open import Data.Bool
open import Data.Maybe
open import Function
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

module Examples (o : Observable) where

B = Observable.B o
D = Observable.D o
d = Observable.d o

ex1 : Cache
ex1 = MkCache B B B id id id id

ex2 : Cache
ex2 = MkCache G C B g ρ ι π
  where
    G = B × Bool
    C = B × Maybe D

    g : G → C
    g (b , full) = (b , (if full then just (d b) else nothing))

    ρ : C → G
    ρ (b , cache) = (b , (maybe (λ _ → true) false cache))

    ι : B → C
    ι b = (b , nothing)

    π : C → B
    π (b , _) = b

ex2good : GoodCache ex2
ex2good = MkGoodCache gρ πι where
  open Cache using (g; ρ; π; ι)

  gρ-lemma : (y : B × Bool) -> (ρ ex2) ((g ex2) y) ≡ y
  gρ-lemma (y , true) = refl
  gρ-lemma (y , false) = refl

  πι-lemma : (y : B) -> (π ex2) ((ι ex2) y) ≡ y
  πι-lemma y = refl

  gρ : ρ ex2 ∘ g ex2 ≡ id
  gρ = funext gρ-lemma
  πι = funext πι-lemma
