open import HProp

module Proofs (AtomicFormula : Set) (η : AtomicFormula → HProp) where

open import Data.Nat using (ℕ ; zero ; suc ; _≤_ ; z≤n ; s≤s)
open import Data.List using ([] ; [_] ; _∷_ ; _++_)

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

Ax2 : (A B : Formula) → (n : ℕ) → [] ⊢ (G (A ⇒ B) ⇒ (G A ⇒ G B)) AT n
Ax2 A B n = ⇒-intro (⇒-intro (
  G-intro (λ m p → ⇒-elim {A = A} 
    (G-elim (hyp (G (A ⇒ B)) n {{∈-here}}) p)
    (G-elim (hyp (G A) n {{∈-there {{∈-here}}}}) p))
  ))

Ax3 : (A : Formula) → (n : ℕ) → [] ⊢ (X (¬ A) ⇔ ¬ (X A)) AT n
Ax3 A n = ∧-intro
  (⇒-intro ( ⇒-intro (⊥-elim {m = suc n} (⇒-elim {A = A} 
    (X-elim (hyp (X (¬ A)) n {{∈-here}})) 
    (X-elim (hyp (X A) n {{∈-there {{∈-here}}}}))
  ))))
  (⇒-intro (X-intro (⇒-intro (⊥-elim {m = n} (⇒-elim {A = (X A)} 
    (hyp (¬ X A) n {{∈-here}}) 
    (X-intro (hyp A (suc n) {{∈-there {{∈-here}}}}))
  )))))

Ax4 : (A B : Formula) (n : ℕ) → [] ⊢ X(A ⇒ B) ⇒ (X A ⇒ X B) AT n
Ax4 A B n = ⇒-intro (⇒-intro (X-intro (⇒-elim {A = A} 
      (X-elim (hyp (X (A ⇒ B)) n {{∈-here}}))
      (X-elim (hyp (X A) n {{∈-there {{∈-here}}}}))
    )))

Ax5 : (A : Formula) (n : ℕ) → [] ⊢ G A ⇒ A ∧ X G A AT n
Ax5 A n = ⇒-intro (∧-intro 
    (G-elim {n = n} {m = n} (hyp (G A) n {{∈-here}}) (n≤n n)) 
    (X-intro (G-intro λ m sn≤m → G-elim {n = n} {m = m} (hyp (G A) n {{∈-here}}) (sn≤m⇒n≤m sn≤m)))
  )

lemma : (A : Formula) (n m : ℕ) → n ≤ m → G (A ⇒ X A) at n ∷ [ A at n ] ⊢ A AT m 
lemma A zero zero p = hyp A zero {{∈-there {{∈-here}}}}
-- have to split cases n = (suc m) or n <= m
lemma A n (suc m) p = {!  p !}

{- lemma A .zero (suc m) z≤n = X-elim (⇒-elim {A = A} 
    (G-elim {n = zero} (hyp (G (A ⇒ X A)) zero {{∈-here}}) z≤n) 
    (lemma A zero m z≤n)
  )
lemma A (suc k) (suc m) (s≤s {k} {m} p) = {!  hyp A (suc m) {{∈-there {{∈-here}}}} !} -}

Ax6 : (A : Formula) (n : ℕ) → [] ⊢ G (A ⇒ X A) ⇒ (A ⇒ G A) AT n 
Ax6 A n = ⇒-intro (⇒-intro (G-intro λ m n≤m → {! m  !}
  ))  