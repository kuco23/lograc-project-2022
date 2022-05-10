open import HProp

module Soundness (AtomicFormula : Set) (η : AtomicFormula → HProp) where

open import Data.Nat using (ℕ ; suc ; _≤_)
open import Data.Product using (_,_)

import Logic
import Semantics
import NaturalDeduction

open module L = Logic AtomicFormula
open module S = Semantics AtomicFormula η
open module ND = NaturalDeduction AtomicFormula

⟦_⟧ʰ : (Δ : Hypotheses) → HProp
⟦ [] ⟧ʰ = ⊤ʰ
⟦ δ at n ∷ Δ ⟧ʰ = ⟦ δ ⟧ n ∧ʰ ⟦ Δ ⟧ʰ

obvious : {n : ℕ} {(δ at n) : TimeFormula} {Δ : Hypotheses} → (δ at n) ∈ Δ → proof(⟦ Δ ⟧ʰ) → proof(⟦ δ ⟧ n)
obvious ∈-here (p , q) = p
obvious ∈-there (p , q) = {! obvious _   !}

Soundness : {Δ : Hypotheses} {δ : Formula} {n : ℕ} → Δ ⊢ δ AT n → proof(⟦ Δ ⟧ʰ) → proof(⟦ δ ⟧ n)
Soundness (weaken φ x) p = {!!}
Soundness (contract φ x) p = {!!}
Soundness (exchange φ₁ φ₂ x) p = {!!}
Soundness (hyp _ _) p = {!!}
Soundness (⊥-elim x) p = {!!}
Soundness (⇒-intro x) p = {!!}
Soundness (⇒-elim x x₂) p = {!!}
Soundness (X-intro x) p = {!!}
Soundness (X-elim x) p = {!!}
Soundness (G-intro x) p = {!!}
Soundness (G-elim x x₂) p = {!!}
  