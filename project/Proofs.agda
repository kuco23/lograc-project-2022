open import Data.Nat using (ℕ ; zero ; suc ; _≤_ ; z≤n ; s≤s)
open import HProp

module Proofs (AtomicFormula : Set) where

open import Data.List using ([] ; [_] ; _∷_ ; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import Data.Nat.Properties using (_≤?_)
open import Relation.Nullary using (yes ; no)
open import AdvancedNumberTheory

import Logic
import NaturalDeduction

open module L = Logic AtomicFormula
open module ND = NaturalDeduction AtomicFormula


Ax2 : (φ ψ : Formula) → (n : ℕ) → [] ⊢ G (φ ⇒ ψ) ⇒ (G φ ⇒ G ψ) AT n
Ax2 φ ψ n = ⇒-intro (⇒-intro (
  G-intro (λ m p → ⇒-elim {φ = φ} 
    (G-elim p (hyp (G (φ ⇒ ψ)) n {{∈-here}}))
    (G-elim p (hyp (G φ) n {{∈-there {{∈-here}}}})))
  ))

Ax3 : (φ : Formula) → (n : ℕ) → [] ⊢ X (¬ φ) ⇔ ¬ (X φ) AT n
Ax3 φ n = ∧-intro
  (⇒-intro ( ⇒-intro (⊥-elim {m = suc n} (⇒-elim {φ = φ} 
    (X-elim (hyp (X (¬ φ)) n {{∈-here}})) 
    (X-elim (hyp (X φ) n {{∈-there {{∈-here}}}}))
  ))))
  (⇒-intro (X-intro (⇒-intro (⊥-elim {m = n} (⇒-elim {φ = (X φ)} 
    (hyp (¬ X φ) n {{∈-here}}) 
    (X-intro (hyp φ (suc n) {{∈-there {{∈-here}}}}))
  )))))

Ax4 : (φ ψ : Formula) (n : ℕ) → [] ⊢ X(φ ⇒ ψ) ⇒ (X φ ⇒ X ψ) AT n
Ax4 φ ψ n = ⇒-intro (⇒-intro (X-intro (⇒-elim {φ = φ} 
      (X-elim (hyp (X (φ ⇒ ψ)) n {{∈-here}}))
      (X-elim (hyp (X φ) n {{∈-there {{∈-here}}}}))
    )))

Ax5 : (φ : Formula) (n : ℕ) → [] ⊢ G φ ⇒ φ ∧ X G φ AT n
Ax5 φ n = ⇒-intro (∧-intro 
    (G-elim {n = n} {m = n} (n≤n n) (hyp (G φ) n {{∈-here}})) 
    (X-intro (G-intro λ m sn≤m → G-elim {n = n} {m = m} (sn≤m⇒n≤m sn≤m) (hyp (G φ) n {{∈-here}})))
  )

Ax6 : (φ : Formula) (n : ℕ) → [] ⊢ G (φ ⇒ X φ) ⇒ (φ ⇒ G φ) AT n 
Ax6 φ n = ⇒-intro (⇒-intro (G-intro λ m n≤m → aux φ n m n≤m)) where
  aux : (φ : Formula) (n m : ℕ) → n ≤ m → G (φ ⇒ X φ) at n ∷ [ φ at n ] ⊢ φ AT m 
  aux φ zero zero p = hyp φ zero {{∈-there {{∈-here}}}}
  aux φ n (suc m) p with (n ≤? m)
  ... | yes q = X-elim (⇒-elim {φ = φ} (G-elim q (hyp (G (φ ⇒ X φ)) n {{∈-here}})) (aux φ n m q))
  ... | no q = aux₁ (n≤sm∧¬n≤m⇒n≡sm p q) (hyp φ n {{∈-there {{∈-here}}}}) where
    aux₁ : n ≡ suc m → G (φ ⇒ X φ) at n ∷ [ φ at n ] ⊢ φ AT n → G (φ ⇒ X φ) at n ∷ [ φ at n ] ⊢ φ AT suc m
    aux₁ refl d = d

{-# TERMINATING #-}
n<m⇒φₙ∈[φ∶n∶m] : {m n : ℕ} {φ : Formula} → suc n ≤ m → (φ at n) ∈ (time-range φ n m)
n<m⇒φₙ∈[φ∶n∶m] {suc zero} {n} (s≤s p) with n ≤? zero 
... | yes z≤n = ∈-here
... | no q = m≤n∧¬m≤n⇒⋆ p q
n<m⇒φₙ∈[φ∶n∶m] {suc (suc m)} {n} (s≤s p) with n ≤? suc m | (suc n) ≤? (suc m)
... | no q₁ | _ = m≤n∧¬m≤n⇒⋆ p q₁
... | yes _ | yes p₁ = ∈-there {{n<m⇒φₙ∈[φ∶n∶m] {suc m} {n} p₁}} -- agda doesn't understand recursion terminates
... | yes _ | no q₁ with n≤sm∧¬n≤m⇒n≡sm p (¬sn≤sm⇒¬n≤m q₁)
...                 | refl = ∈-here

Ax7 : (φ ψ : Formula) (n : ℕ) → [] ⊢ φ U ψ ⇔ ψ ∨ (φ ∧ X (φ U ψ)) AT n
Ax7 φ ψ n = {!!}

Ax8 : (φ ψ : Formula) (n : ℕ) → [] ⊢ φ U ψ ⇒ F ψ AT n
Ax8 φ ψ n = {!!}
