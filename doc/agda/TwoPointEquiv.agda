{-# OPTIONS --without-K --rewriting #-}

module TwoPointEquiv where

open import HoTT

data feq {X : Set} (𝕀 : Set) : (fam : 𝕀 → X) → Set where
  frefl : (x : X) → feq 𝕀 (λ _ → x)

data f1eq {X : Set} (𝕀 : Set) : (fam : 𝕀 → X) → Set where
  f1refl : (x : X) (f : 𝕀 → X) (e : (λ _ → x) == f) → f1eq 𝕀 f

data req {X : Set} (𝕀 : Set) : (fam : 𝕀 → X) → Set where
  rrefl : (x : X) (f : 𝕀 → X) (e : (i : 𝕀) → x == f i) → req 𝕀 f

data peq {X : Set} : (fam : Bool → X) → Set where
  prefl : (x : X) (f : Bool → X) (e : (x == f true) × (x == f false)) → peq f

{-- dependent if --}
ifd : {X : Bool → Set} (b : Bool) → X true → X false → X b
ifd true x y = x
ifd false x y = y

{-- η-expansion of dependent if --}
ifηd : {X : Bool → Set} {f : Π Bool X} (x : Bool) → (ifd {X} x (f true) (f false)) == f x
ifηd true = idp
ifηd false = idp

{-- equivalence of dependent function space with pair --}
thmfd : {X : Bool → Set} → (Π Bool X) ≃ (X true × X false)
thmfd {X} = equiv into out zig zag where
  into : (Π Bool X) → (X true × X false)
  into f = f true , f false
  out : (X true × X false) → (Π Bool X)
  out p = λ b → ifd {X} b (fst p) (snd p)
  zig : (b : (X true × X false)) → into (out b) == b
  zig b = pair= idp idp
  zag : (b : Π Bool X) → out (into b) == b
  zag f = λ= (ifηd {f = f})

≃ff1 : {X 𝕀 : Set} (f : 𝕀 → X) → feq 𝕀 f ≃ f1eq 𝕀 f
≃ff1 {X} {𝕀} f = equiv into out zag zig where
  into : feq 𝕀 f → f1eq 𝕀 f
  into (frefl x) = f1refl x (λ _ → x) idp
  out : f1eq 𝕀 f → feq 𝕀 f
  out (f1refl x .f e) = coe (ap (feq 𝕀) e) (frefl x)
  zig : (a : feq 𝕀 f) → out (into a) == a
  zig (frefl x) = idp
  zag : (a : f1eq 𝕀 f) → into (out a) == a
  zag (f1refl x .(λ _ → x) idp) = idp

≃f1r : {X 𝕀 : Set} (f : 𝕀 → X) → f1eq 𝕀 f ≃ req 𝕀 f
≃f1r {X} {𝕀} f = equiv into out zag zig where
  into : f1eq 𝕀 f → req 𝕀 f
  into (f1refl x p q) = rrefl x p (app= q)
  out : req 𝕀 f → f1eq 𝕀 f
  out (rrefl x p q) = f1refl x p (λ= q)
  zig : (a : f1eq 𝕀 f) → out (into a) == a
  zig (f1refl x p q) = ap (f1refl x f) (! (λ=-η q))
  zag : (b : req 𝕀 f) → into (out b) == b
  zag (rrefl x p q) = ap (rrefl x f) (λ= (app=-β q))

≃rp : {X : Set} (f : Bool → X) → req Bool f ≃ peq f
≃rp {X} f = equiv into out zig zag where
  into : req Bool f → peq f
  into (rrefl x _ e) = prefl x f (–> thmfd e)
  out : peq f → req Bool f
  out (prefl x _ e) = rrefl x f (<– thmfd e)
  zig : (b : peq f) → into (out b) == b
  zig (prefl x _ e) = ap (prefl x f) (<–-inv-r (thmfd {X = λ i → x == f i}) e)
  zag : (a : req Bool f) → out (into a) == a
  zag (rrefl x _ e) = ap (rrefl x f) (<–-inv-l (thmfd {X = λ i → x == f i}) e)

≃p== : {X : Set} (f : Bool → X) → peq f ≃ (f true == f false)
≃p== {X} f = equiv into out zig zag where
  into : peq f → (f true == f false)
  into (prefl x _ e) = ! (fst e) ∙ snd e
  out : (f true == f false) → peq f
  out q = prefl (f true) f (idp , q)
  zig = λ b → idp
  zag : (a : peq f) → out (into a) == a
  zag (prefl _ _ (idp , _)) = idp

finally : {X : Set} (x y : X) → feq Bool (λ b → if b then x else y) == (x == y)
finally x y = lem (λ b → if b then x else y) where
  lem : {X : Set} (f : Bool → X) → feq Bool f == (f true == f false)
  lem f = ua (≃ff1 f) ∙ ua (≃f1r f) ∙ ua (≃rp f) ∙ ua (≃p== f)

{- interesting lemmas I didn't use:

thmΣ : {A : Set} {B : A → Set} (s : Σ A B) (a : A) (p : fst s == a) → s == (a , transport B p (snd s))
thmΣ s .(fst s) idp = idp

boolexte : {X : Set} (f g : Bool → X) → ((f true == g true) × (f false == g false)) ≃ (f == g)
boolexte f g = λ=-equiv ∘e lem where
  lem : ((f true == g true) × (f false == g false)) ≃ (f ∼ g)
  lem = equiv into out zig zag where
    into : ((f true == g true) × (f false == g false)) → f ∼ g
    into (a , b) = λ { true → a ; false → b }
    out : f ∼ g → ((f true == g true) × (f false == g false))
    out e = e true , e false
    zig : (b : f ∼ g) → into ( b true , b false ) == b
    zig b = λ= (λ { true → idp ; false → idp })
    zag : (b : ((f true == g true) × (f false == g false))) → out (into b) == b
    zag (a , b) = pair= idp idp

λ=idp : {A : Set} {P : A → Set} {f : Π A P} → idp == λ= {f = f} (λ _ → idp)
λ=idp = λ=-η idp

weird : {X 𝕀 : Set} (P : (f g : 𝕀 → X) (e : f == g) → Set)
  → (f g : 𝕀 → X) (e : f == g) → P f f idp → P f g e
weird P f .f idp q = q

-}
