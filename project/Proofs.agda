open import Data.Nat using (ℕ ; zero ; suc ; _≤_ ; z≤n ; s≤s)
open import HProp

module Proofs (AtomicFormula : Set) (η : ℕ → AtomicFormula → HProp) where

open import Data.Nat.Properties using (_≤?_)
open import Data.List using ([] ; [_] ; _∷_ ; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Data.Empty renaming (⊥-elim to neg-elim)
open import Relation.Nullary renaming (¬_ to neg_)

import Logic
import Semantics
import NaturalDeduction

open module L = Logic AtomicFormula
open module S = Semantics AtomicFormula η
open module ND = NaturalDeduction AtomicFormula

n≤n : (n : ℕ) → n ≤ n 
n≤n zero = z≤n
n≤n (suc n) = s≤s (n≤n n)

sn≤m⇒n≤m : {n m : ℕ} → suc n ≤ m → n ≤ m 
sn≤m⇒n≤m {zero} p = z≤n
sn≤m⇒n≤m {suc n} (s≤s p) = s≤s (sn≤m⇒n≤m p)

n≤sm∧¬n≤m⇒n≡sm : (n m : ℕ) → (n ≤ suc m) → (neg n ≤ m) → n ≡ (suc m)
n≤sm∧¬n≤m⇒n≡sm zero zero z≤n q = neg-elim (q z≤n)
n≤sm∧¬n≤m⇒n≡sm (suc n) zero (s≤s p) q = cong suc (aux p) where
  aux : (n ≤ zero) → n ≡ zero
  aux z≤n = refl
n≤sm∧¬n≤m⇒n≡sm zero (suc m) z≤n q = neg-elim (q z≤n)
n≤sm∧¬n≤m⇒n≡sm (suc n) (suc m) (s≤s p) q = cong suc (n≤sm∧¬n≤m⇒n≡sm n m p (aux q)) where
  aux : (neg suc n ≤ suc m) → neg n ≤ m
  aux x r = x (s≤s r)

Ax2 : (φ ψ : Formula) → (n : ℕ) → [] ⊢ G (φ ⇒ ψ) ⇒ (G φ ⇒ G ψ) AT n
Ax2 φ ψ n = ⇒-intro (⇒-intro (
  G-intro (λ m p → ⇒-elim {φ = φ} 
    (G-elim (hyp (G (φ ⇒ ψ)) n {{∈-here}}) p)
    (G-elim (hyp (G φ) n {{∈-there {{∈-here}}}}) p))
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
    (G-elim {n = n} {m = n} (hyp (G φ) n {{∈-here}}) (n≤n n)) 
    (X-intro (G-intro λ m sn≤m → G-elim {n = n} {m = m} (hyp (G φ) n {{∈-here}}) (sn≤m⇒n≤m sn≤m)))
  )

Ax6 : (φ : Formula) (n : ℕ) → [] ⊢ G (φ ⇒ X φ) ⇒ (φ ⇒ G φ) AT n 
Ax6 φ n = ⇒-intro (⇒-intro (G-intro λ m n≤m → aux φ n m n≤m)) where
  aux : (φ : Formula) (n m : ℕ) → n ≤ m → G (φ ⇒ X φ) at n ∷ [ φ at n ] ⊢ φ AT m 
  aux φ zero zero p = hyp φ zero {{∈-there {{∈-here}}}}
  aux φ n (suc m) p with (n ≤? m)
  ... | yes q = X-elim (⇒-elim {φ = φ} (G-elim (hyp (G (φ ⇒ X φ)) n {{∈-here}}) q) (aux φ n m q))
  ... | no q = aux₁ (n≤sm∧¬n≤m⇒n≡sm n m p q) (hyp φ n {{∈-there {{∈-here}}}}) where
    aux₁ : n ≡ suc m → G (φ ⇒ X φ) at n ∷ [ φ at n ] ⊢ φ AT n → G (φ ⇒ X φ) at n ∷ [ φ at n ] ⊢ φ AT suc m
    aux₁ refl d = d
