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

triv : Cache
triv = MkCache B B B id id id id

pull : Cache
pull = MkCache G C B g ρ ι π
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

pull-good : GoodCache pull
pull-good = MkGoodCache gρ πι where
  open Cache using (g; ρ; π; ι)

  gρ-lemma : (y : B × Bool) -> ρ pull (g pull y) ≡ y
  gρ-lemma (y , true) = refl
  gρ-lemma (y , false) = refl

  πι-lemma : (y : B) -> π pull (ι pull y) ≡ y
  πι-lemma y = refl

  gρ : ρ pull ∘ g pull ≡ id
  gρ = funext gρ-lemma
  πι = funext πι-lemma

pull-recompute : (B -> B) -> CacheMorphism pull pull
pull-recompute f = MkCacheMorphism fbar fgρ fπι where
  open Cache using (C; g; ρ; π; ι)
  fbar : C pull -> C pull
  fbar (b , _) = f b , nothing

  fgρ-lemma : (x : B × Bool) -> g pull (ρ pull (fbar (g pull x))) ≡ fbar (g pull x)
  fgρ-lemma (y , true) = refl
  fgρ-lemma (y , false) = refl

  fgρ : g pull ∘ ρ pull ∘ fbar ∘ g pull ≡ fbar ∘ g pull
  fgρ = funext fgρ-lemma

  fπι-lemma : (x : B × Maybe D) -> π pull (fbar (ι pull (π pull x))) ≡ π pull (fbar x)
  fπι-lemma (b , just x) = refl
  fπι-lemma (b , nothing) = refl

  fπι : π pull ∘ fbar ∘ ι pull ∘ π pull ≡ π pull ∘ fbar
  fπι = funext fπι-lemma

pull-freshen : CacheMorphism pull pull
pull-freshen = MkCacheMorphism fbar fgρ fπι where
  open Cache using (C; g; ρ; π; ι)
  fbar : C pull -> C pull
  fbar (b , _) = b , just (d b)

  fgρ-lemma : (x : B × Bool) -> g pull (ρ pull (fbar (g pull x))) ≡ fbar (g pull x)
  fgρ-lemma (y , true) = refl
  fgρ-lemma (y , false) = refl

  fgρ : g pull ∘ ρ pull ∘ fbar ∘ g pull ≡ fbar ∘ g pull
  fgρ = funext fgρ-lemma

  fπι-lemma : (x : B × Maybe D) -> π pull (fbar (ι pull (π pull x))) ≡ π pull (fbar x)
  fπι-lemma (b , just x) = refl
  fπι-lemma (b , nothing) = refl

  fπι : π pull ∘ fbar ∘ ι pull ∘ π pull ≡ π pull ∘ fbar
  fπι = funext fπι-lemma
