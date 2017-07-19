{-# OPTIONS --without-K --rewriting #-}

module Parametricity where

open import HoTT hiding (ℤ ; ⊤ ; tt)

postulate
  param : {A B C1 C2 : Set} → (f : ((C : Set) → (A → C) → (B → C))) (g : A → C1) (k : C1 → C2) →
    k ∘ (f _ g) == f _ (k ∘ g)

module EquivFunc {A B : Set} where
  make : ((C : Set) → (A → C) → (B → C)) → B → A
  make f = f A (idf A)

  unmake : (B → A) → ((C : Set) → (A → C) → (B → C))
  unmake f C g = g ∘ f

  ezig : (f : (C : Set) → (A → C) → (B → C)) → unmake (f A (idf A)) == f
  ezig f = λ= (λ C → λ= (param f (idf A))) -- This right here is the only use of parametricity

  ezag : (f : B → A) → make (unmake f) == f
  ezag f = idp

  thm : ((C : Set) → (A → C) → (B → C)) ≃ (B → A)
  thm = equiv make unmake ezag ezig

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
    lemma3 f iep = is-eq way rway (app= czag) (app= czig) where
      open EquivFunc using ( make ; unmake ; ezig ; ezag )

      way : B → A
      way = make f

      rf : (C : Set) → (B → C) → (A → C)
      rf C = iep C .is-equiv.g

      rway : A → B
      rway = make rf

      fact : unmake way == f
      fact = ezig f

      rfact : unmake rway == rf
      rfact = ezig rf

      czig : rway ∘ way == idf B
      czig = ezag (rway ∘ way)
        ∙ ap2 (λ x y → make (λ C → x C ∘ y C)) fact rfact
        ∙ ap make (λ= (λ C → λ= (iep C .is-equiv.f-g)))

      czag : way ∘ rway == idf A
      czag = ezag (way ∘ rway)
        ∙ ap2 (λ x y → make (λ C → x C ∘ y C)) rfact fact
        ∙ ap make (λ= (λ C → λ= (iep C .is-equiv.g-f)))

    lemma4 : (b : B → A) → is-equiv b → (C : Set) → is-equiv (λ (k : A → C) → k ∘ b)
    lemma4 b ie C = is-eq (λ k x → k (b x)) (λ h → h ∘ ie .is-equiv.g)
      (λ h → λ= (λ x → ap h (ie .is-equiv.g-f x)))
      (λ h → λ= (λ x → ap h (ie .is-equiv.f-g x)))

  final : ((C : Set) → (A → C) ≃ (B → C)) ≃ (B ≃ A)
  final = main2 ∘e main1
