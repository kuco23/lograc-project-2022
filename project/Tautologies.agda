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
open import Data.Product
open import Data.Nat.Properties
open import Data.Empty

Hypotheses = List (Formula)


Axiom8 : (A B : Formula) (n : ℕ) →  proof(⟦ (A U B) ⇒ (F B) ⟧ n)
Axiom8 A B n p = ∥∥-elim (λ x y → fun-ext (λ x₁ → ⊥-elim (x x₁))) (λ { (k , r) q → q k (proj₁ r) (proj₁ (proj₂ r))} ) p
-- ∥∥-elim (is-prop (⟦ B ⟧ m)) (λ { (k , r) → {!!}}) p
-- Need to find a inhabitant of proof() (likely to be a lambda abstraction because of implication)

Axiom2 : (A B : Formula) (n : ℕ) → proof(⟦ G (A ⇒ B) ⇒ (G A ⇒ G B)⟧ n)
Axiom2 A B n p p' m q = {!!}

Axiom3 : (A : Formula) (n : ℕ) → proof(⟦ X (¬ A) ⇔ ¬ (X A) ⟧ n)
Axiom3 A n = {!!}

-- Eksperimentacija s pojmi, da razumema

record Collection : Set where
  constructor B_B_B
  field
    kaka : ℕ
    sraka : ℕ

open Collection public

a = B 5 B 5 B
b = kaka a

c = ⟦ G (⊤ ⇒ ⊤) ⇒ (G ⊤ ⇒ G ⊤)⟧ 5
d = ⟦ ⊤ ⇒ Formula.⊥ ⟧ 3
