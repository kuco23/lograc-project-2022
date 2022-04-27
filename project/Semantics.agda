open import HProp

module Semantics (AtomicFormula : Set) (η : AtomicFormula → HProp) where
      
      open import Logic AtomicFormula

      open import Data.Product hiding (∃)
      open import Data.Sum
      open import Data.Unit renaming (⊤ to One)
      open import Data.Empty renaming (⊥ to Zero)

      open import Data.Nat using (ℕ ; suc)
      open import Data.Bool renaming (_∧_ to _and_; _∨_ to _or_)
      open import Data.Bool.Properties

      open import Relation.Binary.PropositionalEquality using (_≡_; refl)


      ℙ = HProp
      Env = AtomicFormula → ℙ

      ⟦_⟧ : Formula → ℕ  → ℙ
      ⟦ ` P ⟧ n = η P
      ⟦ ⊤ ⟧ n = ⊤ʰ
      ⟦ ⊥ ⟧ n = ⊥ʰ
      ⟦ P ∧ Q ⟧ n = ⟦ P ⟧ n ∧ʰ ⟦ Q ⟧ n
      ⟦ P ∨ Q ⟧ n = ⟦ P ⟧ n ∨ʰ ⟦ Q ⟧ n
      ⟦ P ⇒ Q ⟧ n = ⟦ P ⟧ n ⇒ʰ ⟦ Q ⟧ n
      ⟦ G P ⟧ n = ∀ʰ ℕ ((λ m → (n ≤ʰ m) ⇒ʰ ⟦ P ⟧ m))
      ⟦ P U Q ⟧ n = ∃ʰ ℕ  (λ n' → ((n ≤ʰ n') ∧ʰ ((⟦ Q ⟧) n' ∧ʰ (∀ʰ ℕ (λ m → (((n ≤ʰ m) ∧ʰ (m <ʰ n')) ⇒ʰ ⟦ P ⟧ m))))))
      ⟦ X P ⟧ n = ⟦ P ⟧ (suc n)
