{-# OPTIONS --without-K --rewriting #-}

open import Yoneda
open import HoTT hiding (Bool ; true ; false ; _$_)

module YonedaLemma where

module _ where
  open Cat
  open Func
  open Natr
  into : ∀ {n} {ℂ : Cat {n} {n}} (C : ℂ .Ob) (F : Func {n} {n} {lsucc n} {n} (op ℂ) Sets) → Natr (op ℂ) Sets (yon C) F → F .Obf C
  into {ℂ = ℂ} C F α = α .act C (ℂ .id C)

  out : ∀ {n} {ℂ : Cat {n} {n}} (C : ℂ .Ob) (F : Func {n} {n} {lsucc n} {n} (op ℂ) Sets) → F .Obf C → Natr (op ℂ) Sets (yon C) F
  out {ℂ = ℂ} C F x = MkNatr (λ A g → F .Homf g x) (λ f → λ= (λ z → app= (F .pres∘ f z) x ))
