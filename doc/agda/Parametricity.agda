{-# OPTIONS --without-K --rewriting #-}

module Parametricity where

open import HoTT hiding (ℤ ; ⊤ ; tt)

postulate
--  param : {A B C1 C2 : Set} → (f : ({C : Set} → (A → C) → (B → C))) (k : C1 → C2) (g : A → C1) → f (k ∘ g) == k ∘ (f g)
  param : {A B C1 C2 : Set} → (f : ((C : Set) → (A → C) → (B → C))) (g : A → C1) (k : C1 → C2) →
    k ∘ (f _ g) == f _ (k ∘ g)

module EquivFunc {A B : Set} where
  make : ((C : Set) → (A → C) → (B → C)) → B → A
  make f = f A (idf A)

  unmake : (B → A) → ((C : Set) → (A → C) → (B → C))
  unmake f C g = g ∘ f

  zig : (f : (C : Set) → (A → C) → (B → C)) → unmake (f A (idf A)) == f
  zig f = λ= (λ C → λ= (param f (idf A))) -- This right here is the only use of parametricity

  zag : (f : B → A) → make (unmake f) == f
  zag f = idp

  thm : ((C : Set) → (A → C) → (B → C)) ≃ (B → A)
  thm = equiv make unmake zag zig

module Intermediate {X Y Z : Set} where
  open EquivFunc using ( make ; unmake ; zag )

  ithm : (f : X → Y) (g : Y → Z) → unmake (g ∘ f) == (λ C → unmake f C ∘ unmake g C)
  ithm f g = idp

  ithm2 : (f : X → Y) (g : Y → Z) → g ∘ f == make (λ C → unmake f C ∘ unmake g C)
  ithm2 f g = zag (g ∘ f) ∙ ap make (ithm f g)

module Generally where

  -- a kind of associativity property of sigma types
  sigmaLemma : ∀ {n m} {C : Set n} (P : C → Set m) (Q : (c : C) → P c → Set) →
    ((c : C) → Σ (P c) (Q c)) ≃ Σ ((c : C) → P c) (λ f → (c : C) → Q c (f c))
  sigmaLemma {n} {m} {C} P Q = equiv into out zig zag where
    into : ((c : C) → Σ (P c) (Q c)) → Σ ((c : C) → P c) (λ f → (c : C) → Q c (f c))
    into f = (λ c → f c .fst) , (λ c → f c .snd)
    out : Σ ((c : C) → P c) (λ f → (c : C) → Q c (f c)) → ((c : C) → Σ (P c) (Q c))
    out (p , q) c = (p c) , (q c)
    zig : (b : Σ ((c : C) → P c) (λ f → (c : C) → Q c (f c))) → into (out b) == b
    zig (p , q) = idp
    zag : (f : ((c : C) → Σ (P c) (Q c))) → out (into f) == f
    zag f = idp

  mprop : ∀ {n} (P : Set n) → Set n
  mprop P = (x y : P) → x == y

  mprop-of-is-prop : ∀ {n} (P : Set n) → is-prop P → mprop P
  mprop-of-is-prop P is x y = is x y .fst

  props-all-eq : ∀ {n} {P : Set n} → mprop P → (x y : P) → x == y
  props-all-eq sp x y = sp x y

  mprop-over : ∀ {n} {A : Set n} {x y : A} {P : A → Set n} (ss : (a : A) → mprop (P a))  (bx : P x) (by : P y) (e : x == y) → bx == by [ P ↓ e ]
  mprop-over {x = x} ss bx by idp = props-all-eq (ss x) bx by

  equiv-tactic : ∀ {n m} {A : Set n} {B : Set m} {P : A → Set n} {Q : B → Set m} (e : A ≃ B)
    (into : (a : A) → P a → Q (–> e a))
    (out : (b : B) → Q b → P (<– e b))
    (sP : (a : A) → mprop (P a))
    (sQ : (b : B) → mprop (Q b))
    → Σ A P ≃ Σ B Q
  equiv-tactic {A = A} {B} {P} {Q} e into out sP sQ = equiv binto bout bzig bzag where
    binto : Σ A P → Σ B Q
    binto (a , p) = –> e a , into a p
    bout : Σ B Q → Σ A P
    bout (b , q) = <– e b , out b q
    bzig : (b : Σ B Q) → binto (bout b) == b
    bzig (b , q) = pair= (<–-inv-r e b) (mprop-over sQ (into (fst (bout (b , q))) (snd (bout (b , q)))) q (<–-inv-r e b))
    bzag : (a : Σ A P) → bout (binto a) == a
    bzag (a , p) = pair= (<–-inv-l e a) (mprop-over sP (out (fst (binto (a , p))) (snd (binto (a , p)))) p (<–-inv-l e a))

  pilift : ∀ {n m} {C : Set n} {P : C → Set m} → ((c : C) → mprop (P c)) → mprop ((c : C) → P c)
  pilift {C = C} {P} spf f g = λ= (λ x → spf x (f x) (g x))

module Final {A B : Set} where
  open Generally

  goodfam : ((C : Set) → (A → C) → (B → C)) → Set₁
  goodfam fam = (C : Set) → is-equiv (fam C)

  main1 : ((C : Set) → (A → C) ≃ (B → C)) ≃ Σ ((C : Set) → (A → C) → (B → C)) goodfam
  main1 = sigmaLemma (λ C → (A → C) → B → C) (λ _ → is-equiv)

  main2 : Σ ((C : Set) → (A → C) → (B → C)) goodfam ≃ (B ≃ A)
  main2 = equiv-tactic EquivFunc.thm lemma3 lemma4 pilifted equivs-same where
    pilifted : (a : (C : Set) → (A → C) → B → C) (x y : (c : Set) → is-equiv (a c)) → x == y
    pilifted a = pilift (λ c → mprop-of-is-prop (is-equiv (a c)) is-equiv-is-prop)
    equivs-same : (b : B → A) (x y : is-equiv b) → x == y
    equivs-same b = mprop-of-is-prop (is-equiv b) is-equiv-is-prop

    lemma3 : (f : (C : Set) → (A → C) → B → C) → ((C : Set) → is-equiv (f C)) → is-equiv (f A (idf A))
    lemma3 f iep = is-eq way rway (app= combofact2) (app= combofact) where
      open EquivFunc using ( make ; unmake ; zig ; zag )
      open Intermediate using ( ithm2 )

      way : B → A
      way = make f

      rf : (C : Set) → (B → C) → (A → C)
      rf C = iep C .is-equiv.g

      rway : A → B
      rway = make rf

      fact : unmake way == f
      fact = zig f

      rfact : unmake rway == rf
      rfact = zig rf

      combofact : rway ∘ way == idf B
      combofact = ithm2 way rway
        ∙ ap2 (λ x y → make (λ C → x C ∘ y C)) fact rfact
        ∙ ap make (λ= (λ C → λ= (iep C .is-equiv.f-g)))

      combofact2 : way ∘ rway == idf A
      combofact2 = ithm2 rway way
        ∙ ap2 (λ x y → make (λ C → x C ∘ y C)) rfact fact
        ∙ ap make (λ= (λ C → λ= (iep C .is-equiv.g-f)))

    lemma4 : (b : B → A) → is-equiv b → (C : Set) → is-equiv (λ (k : A → C) → k ∘ b)
    lemma4 b ie C = is-eq (λ k x → k (b x)) (λ h → h ∘ ie .is-equiv.g)
      (λ h → λ= (λ x → ap h (ie .is-equiv.g-f x)))
      (λ h → λ= (λ x → ap h (ie .is-equiv.f-g x)))

  final : ((C : Set) → (A → C) ≃ (B → C)) ≃ (B ≃ A)
  final = main2 ∘e main1

{-
module EquivEquiv where
  easy1 : (A B : Set) → A == B → ((C : Set) → (A → C) ≃ (B → C))
  easy1 A .A idp C = ide (A → C)

  easy : {A B : Set} → A ≃ B → ((C : Set) → (A → C) ≃ (B → C))
  easy {A} {B} e = easy1 A B (ua e)

  hard : {A B : Set} → ((C : Set) → (A → C) ≃ (B → C)) → A ≃ B
  hard {A} {B} e = equiv w z (app= (! zag2 ∙ zag)) (app= (! zig2 ∙ zig)) where
    part1 : {C : Set} → (A → C) → B → C
    part1 {C} = –> (e C)
    part2 : {C : Set} → (B → C) → A → C
    part2 {C} = <– (e C)
    part1param : (C1 C2 : Set) (k : C1 → C2) (g : A → C1) → part1 (k ∘ g) == k ∘ (part1 g)
    part1param C1 C2 k g = param part1 k g
    part2param : (C1 C2 : Set) (k : C1 → C2) (g : B → C1) → part2 (k ∘ g) == k ∘ (part2 g)
    part2param C1 C2 k g = param part2 k g

    z : B → A
    z = part1 {A} (idf A)
    zfact : {C2 : Set} (k : A → C2) → part1 k == k ∘ z
    zfact {C2} k = part1param A C2 k (idf A)
    w : A → B
    w = part2 {B} (idf B)
    wfact : {C2 : Set} (k : B → C2) → part2 k == k ∘ w
    wfact {C2} k = part2param B C2 k (idf B)

    zig : part2 (part1 (idf A)) == idf A
    zig = <–-inv-l (e A) (idf A)

    zag : part1 (part2 (idf B)) == idf B
    zag = <–-inv-r (e B) (idf B)

    zig2 : part2 (part1 (idf A)) == z ∘ w
    zig2 = ap part2 (zfact (idf A)) ∙ wfact z

    zag2 : part1 (part2 (idf B)) == w ∘ z
    zag2 = ap part1 (wfact (idf B)) ∙ zfact w


  bigZig1 : {A B : Set} (e : A == B) → hard (easy1 A B (ua (coe-equiv e))) == (coe-equiv e)
  bigZig1 {A} {B} idp = (ap (λ z → hard (easy1 A B z)) (ua-η idp)) ∙ {!!}

  bigZig : {A B : Set} (e : A ≃ B) → hard (easy e) == e
  bigZig e = coe (ap (λ z → hard (easy z) == z) (coe-equiv-β e)) (bigZig1 (ua e))
-}
