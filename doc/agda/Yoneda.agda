{-# OPTIONS --without-K --rewriting #-}

open import HoTT hiding (Bool ; true ; false ; _$_)

module Yoneda where

record Cat {no nm} : Set (lsucc (lmax no nm)) where
  constructor MkCat
  field
    Ob : Set no
    Hom : Ob → Ob → Set nm
    _⊚_ : {A B C : Ob} → Hom B C → Hom A B → Hom A C
    id : (A : Ob) → Hom A A
    assoc : {A B C D : Ob} (h : Hom A B) (g : Hom B C) (f : Hom C D) → ((f ⊚ g) ⊚ h) == (f ⊚ (g ⊚ h))
    ℓid : {A B : Ob} (f : Hom A B) → (id B ⊚ f) == f
    rid : {A B : Ob} (f : Hom A B) → (f ⊚ id A) == f

record Func {nco ncm ndo ndm} (ℂ : Cat {nco} {ncm}) (𝔻 : Cat {ndo} {ndm}) : Set (lmax (lmax nco ncm) (lmax ndo ndm)) where
  constructor MkFunc
  open Cat
  field
    Obf : ℂ .Ob → 𝔻 .Ob
    Homf : {A B : ℂ .Ob} → ℂ .Hom A B → 𝔻 .Hom (Obf A) (Obf B)
    presid : {A : ℂ .Ob} → Homf (ℂ .id A) == 𝔻 .id (Obf A)
    pres∘ : {A B C : ℂ .Ob} (f : ℂ .Hom B C) (g : ℂ .Hom A B) → Homf (ℂ ._⊚_ f g) == 𝔻 ._⊚_ (Homf f) (Homf g)

module _ {nco ncm ndo ndm} (ℂ : Cat {nco} {ncm}) (𝔻 : Cat {ndo} {ndm}) where
  record Natr (F G : Func {nco} {ncm} {ndo} {ndm} ℂ 𝔻) : Set (lmax (lmax nco ncm) (lmax ndo ndm)) where
    constructor MkNatr
    open Cat
    open Func
    field
      act : (A : ℂ .Ob) → 𝔻 .Hom (F .Obf A) (G .Obf A)
      .nat : {A B : ℂ .Ob} (f : ℂ .Hom A B) → 𝔻 ._⊚_ (act B) (F .Homf f) == 𝔻 ._⊚_ (G .Homf f) (act A)

  Natr= : {F G : Func ℂ 𝔻} {α β : Natr F G} → (Natr.act α) == (Natr.act β) → α == β
  Natr= {α = MkNatr act nat} {MkNatr .act nat₁} idp = idp

  NatrId : (F : Func ℂ 𝔻) → Natr F F
  NatrId F = MkNatr (λ A → 𝔻 .id (F .Obf A)) (λ f → (𝔻 .ℓid (F .Homf f)) ∙ (!(𝔻 .rid (F .Homf f)))) where open Cat ; open Func

  NatrComp : {F G H : Func ℂ 𝔻} → Natr G H → Natr F G → Natr F H
  NatrComp {F} {G} {H} α β = final where
    open Cat
    open Func
    open Natr
    _$_ : {A B C : Ob 𝔻} → Hom 𝔻 B C → Hom 𝔻 A B → Hom 𝔻 A C
    _$_ = 𝔻 ._⊚_
    final : Natr F H
    final = MkNatr (λ A → 𝔻 ._⊚_ (α .act A) (β .act A) ) (λ {A} {B} f → 𝔻 .assoc _ _ _ ∙ (ap (λ z → (α .act B) $ z) (β .nat f)) ∙ (! (𝔻 .assoc _ _ _)) ∙ (ap (λ z → z $ (β .act A)) (α .nat f)) ∙ 𝔻. assoc _ _ _)

  FuncCat : Cat {lmax (lmax nco ncm) (lmax ndo ndm)} {lmax (lmax nco ncm) (lmax ndo ndm)}
  FuncCat = MkCat (Func ℂ 𝔻) Natr NatrComp NatrId (λ h g f → Natr= (λ= (λ x → 𝔻 .assoc _ _ _))) (λ f → Natr= (λ= (λ x → 𝔻 .ℓid _))) (λ f → Natr= (λ= (λ x → 𝔻 .rid _))) where open Cat

op : ∀ {no} {nm} → Cat {no} {nm} → Cat {no} {nm}
op (MkCat Ob Hom _⊚_ id assoc ℓid rid) = MkCat Ob (λ A B → Hom B A) (λ f g → g ⊚ f) id (λ h g f → ! (assoc f g h)) rid ℓid

Sets : ∀ {n} → Cat {lsucc n} {n}
Sets {n} = MkCat (Set n) (λ A B → A → B) (λ f g x → f (g x)) (λ _ x → x) (λ h g f → idp) (λ f → λ= (λ x → idp)) (λ f → λ= (λ x → idp))


module _ where
  open Cat
  yon : ∀ {n} {ℂ : Cat {n} {n}} (C : ℂ .Ob) → Func {n} {n} {lsucc n} {n} (op ℂ) Sets
  yon {ℂ = ℂ} C = MkFunc (λ D → ℂ .Hom D C) (λ f g → ℂ ._⊚_ g f) (λ= (λ g → ℂ .rid g)) (λ f g → λ= (λ h →  ! (ℂ .assoc f g h)))

  yonNatr : ∀ {n} {ℂ : Cat {n} {n}} {A B : ℂ .Ob} → ℂ .Hom A B → FuncCat (op ℂ) Sets .Hom (yon A) (yon B)
  yonNatr {ℂ = ℂ} f = MkNatr (λ A x → ℂ ._⊚_ f x ) (λ g → λ= (λ h → ! (ℂ .assoc _ _ _)))


module _ where
  open Cat
  coyon : ∀ {n} {ℂ : Cat {n} {n}} (C : ℂ .Ob) → Func {n} {n} {lsucc n} {n} ℂ Sets
  coyon {ℂ = ℂ} C = MkFunc (λ D → ℂ .Hom C D) (λ f g → ℂ ._⊚_ f g) (λ= (λ g → ℂ .ℓid g)) (λ f g → λ= (λ h → ℂ .assoc h g f))

  coyonNatr : ∀ {n} {ℂ : Cat {n} {n}} {A B : ℂ .Ob} → ℂ .Hom A B → FuncCat ℂ Sets .Hom (coyon B) (coyon A)
  coyonNatr {ℂ = ℂ} f = MkNatr (λ _ x → ℂ ._⊚_ x f) (λ g → λ= (λ h → ℂ .assoc _ _ _))
