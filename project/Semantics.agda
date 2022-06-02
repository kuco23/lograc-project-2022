open import Data.Nat using (ℕ ; suc)
open import HProp

module Semantics (AtomicFormula : Set) (η : ℕ → AtomicFormula → HProp) where

      open import Logic AtomicFormula

      ℙ = ℕ → HProp

      ⟦_⟧ : Formula → ℙ
      ⟦ ` P ⟧ n = η n P
      ⟦ ⊤ ⟧ n = ⊤ʰ
      ⟦ ⊥ ⟧ n = ⊥ʰ
      ⟦ P ∧ Q ⟧ n = ⟦ P ⟧ n ∧ʰ ⟦ Q ⟧ n
      ⟦ P ∨ Q ⟧ n = ⟦ P ⟧ n ∨ʰ ⟦ Q ⟧ n
      ⟦ P ⇒ Q ⟧ n = ⟦ P ⟧ n ⇒ʰ ⟦ Q ⟧ n
      ⟦ X P ⟧ n = ⟦ P ⟧ (suc n)
      ⟦ G P ⟧ n = ∀ʰ ℕ ((λ m → (n ≤ʰ m) ⇒ʰ ⟦ P ⟧ m))
      ⟦ P U Q ⟧ n = ∃ʰ ℕ  (λ n' → (
                  (n ≤ʰ n') ∧ʰ ((⟦ Q ⟧) n' ∧ʰ (∀ʰ ℕ (λ m → (
                              ((n ≤ʰ m) ∧ʰ (m <ʰ n')) ⇒ʰ ⟦ P ⟧ m
                        ))))
            )) 