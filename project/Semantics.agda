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
      ⟦ P U Q ⟧ n = ∃ʰ ℕ  (λ n' → (
                  (n ≤ʰ n') ∧ʰ ((⟦ Q ⟧) n' ∧ʰ (∀ʰ ℕ (λ m → (
                              ((n ≤ʰ m) ∧ʰ (m <ʰ n')) ⇒ʰ ⟦ P ⟧ m
                        ))))
            )) 
      
      open import Data.Unit using (tt)
      open import Data.Nat
      open import Data.Product using (_,_ ; proj₁ ; proj₂)

      n≤n : {n : ℕ} → n ≤ n 
      n≤n {zero} = z≤n
      n≤n {suc n} = s≤s n≤n
      
      absurd : {m n : ℕ} {A : Formula} → proof(⟦ A ⟧ n) → proof(⟦ A ⟧ m)
      absurd {m} {n} {` x} p = p
      absurd {m} {n} {⊤} p = tt
      absurd {m} {n} {⊥} p = p
      absurd {m} {n} {A ∧ A₁} p = (absurd {A = A} (proj₁ p)) , (absurd  {A = A₁} (proj₂ p))
      absurd {m} {n} {A ∨ A₁} p = {!   !}
      absurd {m} {n} {A ⇒ A₁} p q with p (absurd {n} {m} {A} q)
      ... | x = absurd {m} {n} {A₁} x
      absurd {m} {n} {G A} p = λ k q → absurd {k} {n} {A} (p n n≤n)
      absurd {m} {n} {A U A₁} = {!   !}
      absurd {m} {n} {X A} p = absurd {suc m} {suc n} {A} p