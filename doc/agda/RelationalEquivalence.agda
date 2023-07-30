{-# OPTIONS --without-K --rewriting #-}

module RelationalEquivalence where

open import HoTT hiding ( Rel )

Rel : (A B : Set) → Set₁
Rel A B = A → B → Set

Converse : {A B : Set} → Rel A B → Rel B A
Converse R = (λ b a → R a b)

isFunc : {A B : Set} → Rel A B → Set
isFunc {A} {B} R = (a : A) → is-contr (Σ B (R a))

Frel : (A B : Set) → Set₁
Frel A B = Σ (Rel A B) isFunc

funcOfFrel : {A B : Set} → Frel A B → A → B
funcOfFrel (_ , ifn) a = ifn a .fst .fst

Xrof : {A B : Set} → (A → B) → A → B → Set
Xrof f a b = f a == b



canonPath : {A : Set} (ic : is-contr A) (a b : A) → a == b
canonPath ic a b = ! (ic .snd a) ∙ (ic .snd b)

contrLem : {A : Set} (ic : is-contr A) {a b : A} (p : a == b) → canonPath ic a b == p
contrLem ic {a} idp = !-inv-l (ic .snd a)

contrLem2 : {B : Set} {R : B → Set} (ic : is-contr (Σ B R)) → is-contr (R (ic .fst .fst))
contrLem2 (c , π) = (c .snd) , (λ y → {!π (c .fst , y)!}) where

foo0 : {B : Set} {R : B → Set} (cb : B) (cr : R cb) (path1 : (b : B) (r : R b) → cb == b) (path2 : (b : B) (r : R b) → cr == r [ R ↓ path1 b r ])
       (b : B) (ρ1 ρ2 : R b) → ρ1 == ρ2
foo0 cb cr path1 path2 b ρ1 ρ2 = coe {!!} (!ᵈ (path2 b ρ1) ∙ᵈ (path2 b ρ2))

-- (!-inv-l (path1 b ρ1))

 -- (!ᵈ (path2 b ρ1) ∙ᵈ (path2 b ρ2))
foo1 : {B : Set} {R : B → Set} (ic : is-contr (Σ B R)) (b : B) (ρ1 ρ2 : R b) → ρ1 == ρ2
foo1 {R = R} ic@((cb , cr) , π) b ρ1 ρ2 = coe lem (!ᵈ (apd snd (π (b , ρ1))) ∙ᵈ (apd snd (π (b , ρ2)))) where

  lem : PathOver (λ z → R (fst z)) (! (π (b , ρ1)) ∙ π (b , ρ2)) ρ1 ρ2 == (ρ1 == ρ2)
  lem = {!apd fst ( ! (π (b , ρ1)) ∙ π (b , ρ2))!}

foo2 : {B : Set} {R : B → Set} (ic : is-contr (Σ B R)) (b : B) (ρ1 ρ2 : R b)  → ic .fst .fst == b →  ρ1 == ρ2
foo2 ic@(c , π) b ρ1 ρ2 idp = {!!}

foo : {B : Set} {R : B → Set} (ic : is-contr (Σ B R)) (b : B) (ρ1 ρ2 : R b)  → ρ1 == ρ2
foo ic@(c , π) b ρ1 ρ2 = foo2 ic b ρ1 ρ2 (ap fst (ic .snd (b , ρ1)))


Xrof-lem3 : {B : Set} (R : B → Set) (rif : is-contr (Σ B R)) (b : B) → (rif .fst .fst == b) ≃ R b
Xrof-lem3 {B} R rif b = equiv into out zig zag where
  center = rif .fst
  path = rif .snd
  into : center .fst == b → R b
  into idp = center .snd
  out : R b → center .fst == b
  out r = ap fst (path (b , r))

  zigm : (r : R b) (z : fst rif == b , r) → into (ap fst z) == transport R (ap fst z) (center .snd)
  zigm r idp = idp Σ A R


  zig : (r : R b) → into (ap fst (path (b , r))) == r
  zig r = zigm r (path (b , r)) ∙ {!!}

  zag : (q : center .fst == b) → out (into q) == q
  zag idp = ap (ap fst) (! (contrLem rif _) ∙ contrLem rif _)


Xrof-lem2 : {A B : Set} (R : Rel A B) (a : A) (rif : is-contr (Σ B (R a)))  (b : B) → (rif .fst .fst == b) ≃ R a b
Xrof-lem2 {A} {B} R a rif b = Xrof-lem3 {B} (R a) rif b

Xrof-lem : {A B : Set} (R : Rel A B) (rif : isFunc R) → Xrof (λ a → rif a .fst .fst) == R
Xrof-lem {A} {B}  R rif = λ= (λ a → λ= (λ b → ua (Xrof-lem2 R a (rif a) b)))


Xlem : {A B : Set} (f : A → B) (a : A) → (y : Σ B (Xrof f a)) → f a , idp == y
Xlem f a (_ , idp) = idp

Xrif : {A B : Set} (f : A → B) → isFunc (Xrof f)
Xrif f a = ((f a) , idp) , (Xlem f a)

frelOfFunc : {A B : Set} → (A → B) → Frel A B
frelOfFunc {A} {B} f = (Xrof f , Xrif f)



zig : {A B : Set} (f : A → B) → funcOfFrel (frelOfFunc f) == f
zig f = idp

zag : {A B : Set} (f : Frel A B) → frelOfFunc (funcOfFrel f) == f
zag (R , rif) = lem where
  lem : frelOfFunc (λ a → rif a .fst .fst) == (R , rif)
  lem = pair= (Xrof-lem R rif) {!!}

nice : {A B : Set} → (A → B) ≃ Frel A B
nice = equiv frelOfFunc funcOfFrel zag zig

rIsEquiv : {A B : Set} → Rel A B → Set
rIsEquiv R = isFunc R × isFunc (Converse R)

eRel : (A B : Set) → Set₁
eRel A B = Σ (Rel A B) rIsEquiv

equivInject : {A B : Set} {f : A → B} (ie : is-equiv f) → (b : B) (a1 a2 : A) → f a1 == b → f a2 == b → a1 == a2
equivInject ie _ a1 a2 q idp = ! (ie .is-equiv.g-f a1) ∙ ap (ie .is-equiv.g) q ∙ ie .is-equiv.g-f a2

-- claim : {A B : Set} → (A ≃ B) ≃ (eRel A B)
-- claim {A} {B} = equiv into out zig zag where
--   into : A ≃ B → eRel A B
--   into (f , ie) = (relOfFunc f) , (rofIsFunc f , {!!} )
--   out : eRel A B → A ≃ B
--   out = {!!}
--   zig : (b : eRel A B) → into (out b) == b
--   zig = {!!}
--   zag : (a : A ≃ B) → out (into a) == a
--   zag = {!!}

{-
Rel : (A B : Set) → Set₁
Rel A B = A → B → Set

Converse : {A B : Set} → Rel A B → Rel B A
Converse R = (λ b a → R a b)

Total : {A B : Set} → Rel A B → Set
Total {A} {B} R = (a : A) → Σ B (λ b → R a b)

Single : {A B : Set} → Rel A B → Set
Single {A} {B} R = (a : A) (b1 b2 : B) → R a b1 → R a b2 → b1 == b2

isFunc : {A B : Set} → Rel A B → Set
isFunc R = Total R × Single R

rIsEquiv : {A B : Set} → Rel A B → Set
rIsEquiv R = isFunc R × isFunc (Converse R)

eRel : (A B : Set) → Set₁
eRel A B = Σ (Rel A B) rIsEquiv

funcOfTotalRel : {A B : Set} {R : Rel A B} → Total R → A → B
funcOfTotalRel tot a = tot a .fst

relOfFunc : {A B : Set} → (A → B) → Rel A B
relOfFunc f a b = f a == b

rofIsFunc : {A B : Set} (f : A → B) → isFunc (relOfFunc f)
rofIsFunc f = {!!}

equivInject : {A B : Set} {f : A → B} (ie : is-equiv f) → (b : B) (a1 a2 : A) → f a1 == b → f a2 == b → a1 == a2
equivInject ie _ a1 a2 q idp = ! (ie .is-equiv.g-f a1) ∙ ap (ie .is-equiv.g) q ∙ ie .is-equiv.g-f a2

claim : {A B : Set} → (A ≃ B) ≃ (eRel A B)
claim {A} {B} = equiv into out zig zag where
  into : A ≃ B → eRel A B
  into (f , ie) = (relOfFunc f) , (rofIsFunc f , (λ b → ie .is-equiv.g b , ie .is-equiv.f-g b) , equivInject ie)
  out : eRel A B → A ≃ B
  out = {!!}
  zig : (b : eRel A B) → into (out b) == b
  zig = {!!}
  zag : (a : A ≃ B) → out (into a) == a
  zag = {!!}
-}
