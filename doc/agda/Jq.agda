module Jq where

{-

functional lenses are neat.

https://medium.com/@dtipson/functional-lenses-d1aba9e52254
https://bartoszmilewski.com/category/lens/
https://bartoszmilewski.com/2015/07/13/from-lenses-to-yoneda-embedding/
https://twanvl.nl/blog/haskell/cps-functional-references
https://arxiv.org/pdf/1103.2841v2.pdf ("Functor is to Lens as Applicative is to Biplate")
https://github.com/ekmett/lens/wiki/History-of-Lenses
http://comonad.com/reader/2012/mirrored-lenses/

-}

open import Level renaming (suc to lsuc)
open import Data.Nat
open import Data.Product hiding (map)
open import Data.List hiding (map)
open import Data.Bool hiding (T)
open import Function using (_∘_)

-- applicatives
record App {n} : Set (lsuc n)  where
  constructor MkApp
  field
    T : Set n → Set n
    η : {X : Set n} → X → T X
    $ : {A B : Set n} → T (A → B) → T A → T B
open App

-- trivial applicative
TrivApp : ∀ {n} → App {n}
TrivApp = MkApp (λ x → x) (λ y → y) (λ f x → f x)

-- output applicative
OutputApp : ∀ {n} → Set n → App {n}
OutputApp {n} R = MkApp (λ A → A × List R) oη o$
  where
  oη : {A : Set n} → A → A × List R
  oη a = (a , [])

  o$ : {A B : Set n} → ((A → B) × List R) → (A × List R) → (B × List R)
  o$ (f , rs1) (a , rs2) = (f a , rs1 ++ rs2)

-- useful definitions
bnd : ∀ {n} (M : App) {A B : Set n} → T M A → (A → B) → T M B
bnd M x f = $ M (η M f) x

pair : ∀ {n} (M : App) {A B : Set n} → T M A → T M B → T M (A × B)
pair M {A} {B} a b = $ M (bnd M a (λ a → λ b → a , b)) b

-- some arbitrary record type for an example
record Foo : Set where
  constructor MkFoo
  inductive
  field
    Alice : ℕ
    Bob : Bool
    Carol : List Foo
open Foo

-- cursor peeking at a set of values of type α in a larger type β
cursor : ∀ {n} → Set n → Set n → Set (lsuc n)
cursor {n} α β = (M : App {n}) → (α → T M α) → β → T M β

jq[] : {A : Set} → cursor A (List A)
jq[] M f [] = η M []
jq[] M f (h ∷ tl) = bnd M (pair M (f h) (jq[] M f tl)) cons
  where
  cons : {A : Set} → A × List A → List A
  cons (a , as) = a ∷ as

jqAlice : cursor ℕ Foo
jqAlice M f x = bnd M (f (Alice x)) (λ a → record x { Alice = a })

jqBob : cursor Bool Foo
jqBob M f x = bnd M (f (Bob x)) (λ b → record x { Bob = b })

jqCarol : cursor (List Foo) Foo
jqCarol M f x = bnd M (f (Carol x)) (λ c → record x { Carol = c })

select : ∀ {n} {A : Set n} → (A → Bool) → cursor A A
select pred M f x = if pred x then f x else η M x

update : ∀ {n} {α β : Set n} → cursor α β → (α → α) → β → β
update c f x = c TrivApp f x

query : ∀ {n} {α β : Set n} → cursor α β → β → List α
query {α = α} c x = proj₂ (c (OutputApp α) (λ a → (a , a ∷ [])) x)


exampleData : List Foo
exampleData = MkFoo 10 true (MkFoo 20 false [] ∷ MkFoo 30 true [] ∷ []) ∷
              MkFoo 40 false (MkFoo 50 true [] ∷ MkFoo 60 false [] ∷ []) ∷ []
-- like json data
-- [{"alice":10,"bob":true, "carol":[{"alice":20,"bob":false,"carol":[]},{"alice":30,"bob":true, "carol":[]}]},
--  {"alice":40,"bob":false,"carol":[{"alice":50,"bob":true, "carol":[]},{"alice":60,"bob":false,"carol":[]}]}]
_∣_ : ∀ {n} {α β γ : Set n} → cursor β α → cursor γ β → cursor γ α
_∣_ c1 c2 M = c1 M ∘ c2 M
infixr 20 _∣_

exampleCursor : cursor ℕ (List Foo)
exampleCursor = jq[] ∣ jqCarol ∣ jq[] ∣ jqAlice -- like jq '.[].carol[].alice'

queryResult : List ℕ
queryResult = query exampleCursor exampleData
-- normalizes to 20 ∷ 30 ∷ 50 ∷ 60 ∷ []

updateResult : List Foo
updateResult = update exampleCursor (λ x → suc x) exampleData -- like jq '.[].carol[].alice |= . + 1'
-- normalizes to
-- MkFoo 10 true (MkFoo 21 false [] ∷ MkFoo 31 true [] ∷ []) ∷
-- MkFoo 40 false (MkFoo 51 true [] ∷ MkFoo 61 false [] ∷ []) ∷ []

exampleCursor2 : cursor ℕ (List Foo)
-- like jq '(.[] | select(.bob == true) | .carol[] | select(.bob == true) | .alice)'
exampleCursor2 = jq[] ∣ select Bob ∣ jqCarol ∣ jq[] ∣ select Bob ∣ jqAlice

queryResult2 : List ℕ
queryResult2 = query exampleCursor2 exampleData
-- normalizes to 30 ∷ []

updateResult2 : List Foo
-- like jq '(.[] | select(.bob == true) | .carol[] | select(.bob == true) | .alice) |= . + 100'
updateResult2 = update exampleCursor2 (λ x → x + 100) exampleData
-- normalizes to
-- MkFoo 10 true (MkFoo 20 false [] ∷ MkFoo 130 true [] ∷ []) ∷
-- MkFoo 40 false (MkFoo 50 true [] ∷ MkFoo 60 false [] ∷ []) ∷ []

{-------------------------------------------------------------------------------------------
 Coding up the stuff from section 3 of "Functor is to Lens as Applicative is to Biplate"
 -------------------------------------------------------------------------------------------}

-- Comonads
record Functor {n} : Set (lsuc n)  where
  constructor MkFunctor
  field
    F : Set n → Set n
    fmap : {A B : Set n} → (A → B) → (F A → F B)

constFunctor : ∀ {n} (B : Set n) → Functor {n}
constFunctor B = MkFunctor (λ _ → B) (λ _ x → x)

idFunctor : ∀ {n} → Functor {n}
idFunctor = MkFunctor (λ Z → Z) (λ f → f)

-- Comonads
record Comon {n} : Set (lsuc n)  where
  constructor MkComon
  field
    □ : Set n → Set n
    fmap : {A B : Set n} → (A → B) → (□ A → □ B)
    δ : {A : Set n} → □ A → □ (□ A)
    ε : {A : Set n} → □ A → A
open Comon

-- useful
extend : ∀ {n} (C : Comon) {A B : Set n} → (□ C A → B) → □ C A → □ C B
extend C f x = fmap C f (δ C x)

record Coalg {n} (C : Comon {n}) : Set (lsuc n) where
  constructor MkCoalg
  field
    A : Set n
    f : A → □ C A

Store : ∀ {n} → Set n → Set n → Set n
Store B A = B × (B → A)

StoreComon : ∀ {n} → Set n → Comon {n}
StoreComon {n} B = MkComon (Store B) sfmap sδ sε
  where
  sfmap : {X Y : Set n} → (X → Y) → Store B X → Store B Y
  sfmap {X} {Y} f (sb , sf) = sb , (f ∘ sf)

  sδ : {A : Set n} → B × (B → A) → B × (B → B × (B → A))
  sδ (b , f) = b , (λ b → b , f)

  sε : {A : Set n} → B × (B → A) → A
  sε (b , f) = f b

StoreFunctor : ∀ {n} → Set n → Functor {n}
StoreFunctor {n} B = MkFunctor (Store B) sfmap
  where
  sfmap : {X Y : Set n} → (X → Y) → Store B X → Store B Y
  sfmap {X} {Y} f (sb , sf) = sb , (f ∘ sf)


data CartStore {n} (B : Set n) : Set n → Set n where
  Unit : {A : Set n} → A → CartStore B A
  Battery : {A : Set n} → CartStore B (B → A) → B → CartStore B A

CartStoreComon : ∀ {n} → Set n → Comon {n}
CartStoreComon {n} B = MkComon (CartStore B) sfmap sδ sε
  where
  sfmap : {X Y : Set n} → (X → Y) → CartStore B X → CartStore B Y
  sfmap {X} {Y} f (Unit x) = Unit (f x)
  sfmap {X} {Y} f (Battery cs x) = Battery (sfmap (λ g → f ∘ g) cs) x

  sδ : {A : Set n} → CartStore B A → CartStore B (CartStore B A)
  sδ (Unit x) = Unit (Unit x)
  sδ (Battery cs x) = Battery (sfmap Battery (sδ cs)) x

  sε : {A : Set n} → CartStore B A → A
  sε (Unit x) = x
  sε (Battery cs x) = sε cs x

Biplate : ∀ {n} → Set n → Set n → Set n
Biplate A B = A → CartStore B A

{-------------------------------------------------------------------------------------------
  section 4 of "Functor is to Lens as Applicative is to Biplate":
  can I see that Laarhoven supplis equiv to Store?
 -------------------------------------------------------------------------------------------}

Laarhoven : ∀ {n} → Set n → Set n → Set (lsuc n)
Laarhoven {n} α β = (F : Functor {n}) → (α → Functor.F F α) → Functor.F F β

idLens : ∀ {n} (B : Set n) → B → Store B B
idLens B b = b , λ x → x

There : ∀ {n} (A B : Set n) → Laarhoven B A → Store B A
There A B ℓ = ℓ (StoreFunctor B) (idLens B)

Back : ∀ {n} (A B : Set n) → Store B A → Laarhoven B A
Back A B (b , f) F k = Functor.fmap F f (k b)
