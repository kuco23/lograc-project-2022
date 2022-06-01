open import HProp

module Semantics (AtomicFormula : Set) (η : AtomicFormula → HProp) where

      open import Data.Nat using (ℕ ; suc)
      open import Logic AtomicFormula

      ℙ = ℕ → HProp

      ⟦_⟧ : Formula → ℙ
      ⟦ ` P ⟧ n = η P
      ⟦ ⊤ ⟧ n = ⊤ʰ
      ⟦ ⊥ ⟧ n = ⊥ʰ
      ⟦ P ∧ Q ⟧ n = ⟦ P ⟧ n ∧ʰ ⟦ Q ⟧ n
      ⟦ P ∨ Q ⟧ n = ⟦ P ⟧ n ∨ʰ ⟦ Q ⟧ n
      ⟦ P ⇒ Q ⟧ n = ⟦ P ⟧ n ⇒ʰ ⟦ Q ⟧ n
      ⟦ X P ⟧ n = ⟦ P ⟧ (suc n)
      ⟦ G P ⟧ n = ∀ʰ ℕ ((λ m → (n ≤ʰ m) ⇒ʰ ⟦ P ⟧ m))
      ⟦ P U Q ⟧ n = ∃ʰ ℕ  (λ n' → ((n ≤ʰ n') ∧ʰ ((⟦ Q ⟧) n' ∧ʰ (∀ʰ ℕ (λ m → (((n ≤ʰ m) ∧ʰ (m <ʰ n')) ⇒ʰ ⟦ P ⟧ m))))))

      absurd : {n m : ℕ} {A : Formula} → proof(⟦ A ⟧ n) → proof(⟦ A ⟧ m)
      absurd {m} {n} {` x} p = p
      absurd {m} {n} {⊤} p = Agda.Builtin.Unit.tt
      absurd {m} {n} {A ∧ A₁} p = {!   !}
      absurd {m} {n} {A ∨ A₁} p = {!   !}
      absurd {m} {n} {A ⇒ A₁} p = {!   !}
      absurd {m} {n} {G A} p = {!   !}
      absurd {m} {n} {A U A₁} p = {!   !}
      absurd {m} {n} {X A} p = {!   !}