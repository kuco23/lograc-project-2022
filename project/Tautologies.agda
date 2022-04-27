open import HProp

module Tautologies (AtomicFormula : Set) (η : AtomicFormula → HProp)  where

open import Logic AtomicFormula
open import Semantics AtomicFormula η
-- stran 32 na https://www.math.tecnico.ulisboa.pt/~mvolpe/publications/theses/volpe-phd-thesis.pdf

{-
A1 : ( ϕ ψ : Formula) (n : ℕ)
     → [] ⊢ (ϕ ⇒ ψ) ⇒ (ψ ⇒ ψ)

A1 = ?
-}
open import Data.Nat

Hypotheses = List (Formula)

Axiom8 : (A B : Formula) (n : ℕ) → proof (⟦ (A U B) ⇒ (G B) ⟧ n)
Axiom8 A B n = {!   !}
-- Need to find a inhabitant of proof() (likely to be a lambda abstraction because of implication)

Axiom2 : (A B : Formula) (n : ℕ) → proof(⟦ G (A ⇒ B) ⇒ (G A ⇒ G B)⟧ n)
Axiom2 A B n p p' m q = {!!}

Axiom3 : (A : Formula) (n : ℕ) → proof(⟦ X (¬ A) ⇔ ¬ (X A) ⟧ n)
Axiom3 A n = {!!}
