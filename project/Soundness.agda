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
obvious {n} (∈-there {{x}}) (p , q) = obvious {n} x q

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Agda.Builtin.Unit renaming (tt to true) hiding (⊤)

⊤≡⊤∧⊤ : (n : ℕ) → proof(⟦ ⊤ ⇔ ⊤ ∧ ⊤ ⟧ n)
⊤≡⊤∧⊤ = λ n →
            (λ x → true , true) ,
            (λ x → true)

lemma1 : {Δ : Hypotheses} {δ : Formula} {n : ℕ} → Δ ⊢ δ AT n → proof(⟦ Δ ⟧ʰ) → proof(⟦ δ ⟧ n)
lemma1 = {!!}


lemma⟦ : (Δ₁ Δ₂ : Hypotheses) → proof(⟦ Δ₁ ++ Δ₂ ⟧ʰ) → proof(⟦ Δ₁ ⟧ʰ  ∧ʰ ⟦ Δ₂ ⟧ʰ)
lemma⟦ [] Δ₂ p = true , p
lemma⟦ (x ∷ Δ₁) Δ₂ (p , q) with lemma⟦ Δ₁ Δ₂ q
... | u , v = (p , u) , v

lemmasubst : (Δ₁ Δ₂ Δ₃ : Hypotheses) → (φ : TimeFormula) → proof(⟦ Δ₁ ++ Δ₂ ++ Δ₃ ⟧ʰ) → proof(⟦ Δ₁  ++ Δ₃ ++ Δ₂ ⟧ʰ)
lemmasubst = {!!}

Soundness : {Δ : Hypotheses} {δ : Formula} {n : ℕ} → Δ ⊢ δ AT n → proof(⟦ Δ ⟧ʰ) → proof(⟦ δ ⟧ n)

Soundness (weaken {Δ₁} {Δ₂} φ {ψ} {n} x) =  lemmasubst {!!} {!!} {!!} {!!}
{-where
  lemma : (A B C : Formula) → proof(⟦ A ∧ B ∧ C ⟧ n) → proof(⟦ A ∧ C ⟧ n)
  lemma A B C (fst , snd) = fst , Data.Product.proj₂ snd-}

Soundness (contract φ x) p = {!!}

Soundness (exchange φ₁ φ₂ x) p = {!!}

Soundness (hyp _ _) p = {!!}

Soundness (⊥-elim x) p = {!!}

Soundness (⇒-intro x) p = λ x₁ → {!!}

Soundness (⇒-elim x x₂) p = {!!}

Soundness (X-intro x) p = Soundness x p

Soundness (X-elim x) p = Soundness x p

Soundness (G-intro x) p = λ x₁ x₂ → Soundness (x x₁ x₂) p

Soundness (G-elim x x₂) p = {!!}
  
