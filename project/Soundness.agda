open import HProp

module Soundness (AtomicFormula : Set) (η : AtomicFormula → HProp) where

open import Data.Nat using (ℕ ; suc ; _≤_)
open import Agda.Builtin.Unit renaming (tt to true) hiding (⊤)
open import Data.Product using (_,_ ; proj₁ ; proj₂)

import Relation.Binary.PropositionalEquality as Eq
open Eq renaming ([_] to [|_|])
open Eq.≡-Reasoning

import Logic
import Semantics
import NaturalDeduction

open module L = Logic AtomicFormula
open module S = Semantics AtomicFormula η
open module ND = NaturalDeduction AtomicFormula

∧-comm : {φ ψ : HProp} → proof(φ ∧ʰ ψ) → proof(ψ ∧ʰ φ)
∧-comm (p , q) = q , p

⟦_⟧ʰ : (Δ : Hypotheses) → HProp
⟦ [] ⟧ʰ = ⊤ʰ
⟦ δ at n ∷ Δ ⟧ʰ = ⟦ δ ⟧ n ∧ʰ ⟦ Δ ⟧ʰ

⊤≡⊤∧⊤ : (n : ℕ) → proof(⟦ ⊤ ⇔ ⊤ ∧ ⊤ ⟧ n)
⊤≡⊤∧⊤ = λ n → (λ x → true , true) , (λ x → true)

≡to→ : {Δ₁ Δ₂ : Hypotheses} → Δ₁ ≡ Δ₂ → proof(⟦ Δ₁ ⟧ʰ) → proof(⟦ Δ₂ ⟧ʰ)
≡to→ refl = λ z → z

extract : {n : ℕ} {(δ at n) : TimeFormula} {Δ : Hypotheses} → (δ at n) ∈ Δ → proof(⟦ Δ ⟧ʰ) → proof(⟦ δ ⟧ n)
extract ∈-here (p , q) = p
extract {n} (∈-there {{x}}) (p , q) = extract {n} x q

split : (Δ₁ Δ₂ : Hypotheses) → proof(⟦ Δ₁ ++ Δ₂ ⟧ʰ) → proof(⟦ Δ₁ ⟧ʰ ∧ʰ ⟦ Δ₂ ⟧ʰ)
split [] Δ₂ p = true , p
split (x ∷ Δ₁) Δ₂ (p , q) with split Δ₁ Δ₂ q
... | q₁ , q₂ = (p , q₁) , q₂

join : (Δ₁ Δ₂ : Hypotheses) → proof(⟦ Δ₁ ⟧ʰ ∧ʰ ⟦ Δ₂ ⟧ʰ) → proof(⟦ Δ₁ ++ Δ₂ ⟧ʰ)
join [] Δ₂ p = proj₂ p
join (x ∷ Δ₁) Δ₂ p = {!  !}

shuffle : (Δ₁ Δ₂ Δ₃ : Hypotheses) → proof(⟦ Δ₁ ++ Δ₂ ++ Δ₃ ⟧ʰ) → proof(⟦ Δ₁ ++ Δ₃ ++ Δ₂ ⟧ʰ)
shuffle Δ₁ Δ₂ [] = ≡to→ aux where
  aux : Δ₁ ++ Δ₂ ++ [] ≡ Δ₁ ++ [] ++ Δ₂ 
  aux = {!  !}
shuffle Δ₁ Δ₂ (x ∷ []) p = (≡to→ aux₆) (aux₅ (aux₄ (aux₃ (aux₂ (aux₁ p))))) where
  aux₁ : proof(⟦ Δ₁ ++ Δ₂ ++ (x ∷ []) ⟧ʰ) → proof(⟦ Δ₁ ⟧ʰ ∧ʰ ⟦ Δ₂ ++ (x ∷ []) ⟧ʰ )
  aux₁ = split Δ₁ (Δ₂ ++ (x ∷ []))
  aux₂ : proof(⟦ Δ₁ ⟧ʰ ∧ʰ ⟦ Δ₂ ++ (x ∷ []) ⟧ʰ) → proof(⟦ Δ₁ ⟧ʰ ∧ʰ (⟦ Δ₂ ⟧ʰ ∧ʰ ⟦ (x ∷ []) ⟧ʰ))
  aux₂ p = {!   !}
  aux₃ : proof(⟦ Δ₁ ⟧ʰ ∧ʰ (⟦ Δ₂ ⟧ʰ ∧ʰ ⟦ (x ∷ []) ⟧ʰ)) → proof(⟦ Δ₁ ⟧ʰ ∧ʰ (⟦ (x ∷ []) ⟧ʰ ∧ʰ ⟦ Δ₂ ⟧ʰ))
  aux₃ = {!   !}
  aux₄ : proof(⟦ Δ₁ ⟧ʰ ∧ʰ (⟦ (x ∷ []) ⟧ʰ ∧ʰ ⟦ Δ₂ ⟧ʰ)) → proof(⟦ Δ₁ ⟧ʰ ∧ʰ ⟦ (x ∷ []) ++ Δ₂ ⟧ʰ)
  aux₄ = {!   !}
  aux₅ : proof(⟦ Δ₁ ⟧ʰ ∧ʰ ⟦ (x ∷ []) ++ Δ₂ ⟧ʰ) → proof(⟦ Δ₁ ++ ((x ∷ []) ++ Δ₂) ⟧ʰ)
  aux₅ = {!   !}
  aux₆ : Δ₁ ++ ((x ∷ []) ++ Δ₂) ≡ Δ₁ ++ (x ∷ []) ++ Δ₂
  aux₆ = {!   !}
shuffle Δ₁ Δ₂ (x ∷ Δ₃) p = (≡to→ aux₅) (aux₄ ((≡to→ aux₃) (aux₂ ((≡to→ aux₁) p)))) where
  aux₁ : Δ₁ ++ Δ₂ ++ (x ∷ Δ₃) ≡ Δ₁ ++ (Δ₂ ++ (x ∷ [])) ++ Δ₃ 
  aux₁ = {!   !}
  aux₂ : proof(⟦ Δ₁ ++ (Δ₂ ++ (x ∷ [])) ++ Δ₃ ⟧ʰ) → proof(⟦ Δ₁ ++ Δ₃ ++ (Δ₂ ++ (x ∷ [])) ⟧ʰ)
  aux₂ = shuffle Δ₁ (Δ₂ ++ (x ∷ [])) Δ₃
  aux₃ : Δ₁ ++ Δ₃ ++ (Δ₂ ++ (x ∷ [])) ≡ Δ₁ ++ (Δ₃ ++ Δ₂) ++ (x ∷ [])
  aux₃ = {!   !}
  aux₄ : proof(⟦ Δ₁ ++ (Δ₃ ++ Δ₂) ++ (x ∷ []) ⟧ʰ) → proof(⟦ Δ₁ ++ (x ∷ []) ++ (Δ₃ ++ Δ₂) ⟧ʰ)
  aux₄ = shuffle Δ₁ (Δ₃ ++ Δ₂) (x ∷ [])
  aux₅ : Δ₁ ++ (x ∷ []) ++ (Δ₃ ++ Δ₂) ≡ Δ₁ ++ (x ∷ Δ₃) ++ Δ₂
  aux₅ = {!   !}

Soundness : {Δ : Hypotheses} {δ : Formula} {n : ℕ} → Δ ⊢ δ AT n → proof(⟦ Δ ⟧ʰ) → proof(⟦ δ ⟧ n)

Soundness (weaken {Δ₁} {Δ₂} φ {ψ} {n} x) = {!   !}
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
  
