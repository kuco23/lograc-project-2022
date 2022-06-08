open import Data.Nat using (ℕ)
open import HProp

module Tautologies (AtomicFormula : Set) (η : AtomicFormula → ℕ → HProp)  where

open import Data.Product using (_,_ ; proj₁ ; proj₂)

open import Logic AtomicFormula
open import Semantics AtomicFormula η

Axiom8 : (φ ψ : Formula) (n : ℕ) →  proof(⟦ (φ U ψ) ⇒ (F ψ) ⟧ n)
Axiom8 φ ψ n p = ∥∥-elim (is-prop(⟦ F ψ ⟧ n)) (λ (k , r) q → q k (proj₁ r) (proj₁ (proj₂ r))) p

Axiom2 : (φ ψ : Formula) (n : ℕ) → proof(⟦ G (φ ⇒ ψ) ⇒ (G φ ⇒ G ψ)⟧ n)
Axiom2 φ ψ n p = λ q k n≤k → p k n≤k (q k n≤k)

Axiom3 : (φ : Formula) (n : ℕ) → proof(⟦ X (¬ φ) ⇔ ¬ (X φ) ⟧ n)
Axiom3 φ n = (λ x → x) , (λ x → x)

Axiom4 : (φ ψ : Formula) (n : ℕ) → proof(⟦ X(φ ⇒ ψ) ⇒ (X φ ⇒ X ψ) ⟧ n)
Axiom4 φ ψ n p q = p q

Axiom5 : (φ : Formula) (n : ℕ) → proof(⟦ G φ ⇒ φ ∧ X G φ ⟧ n)
Axiom5 φ n x = {!!}