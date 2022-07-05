open import Data.Nat using (ℕ ; zero ; suc ; _≤_ ; _<_ ; z≤n ; s≤s)
open import HProp

module Proofs (AtomicFormula : Set) where

open import Data.Empty renaming (⊥-elim to bot-elim)
open import Data.List using (List ; [] ; [_] ; _∷_ ; _++_)
open import Data.List.Properties using (++-assoc)
open import Data.Nat.Properties using (_≤?_ ; ≤-refl ; ≤-trans ; ≤-antisym ; ≰⇒> ; <⇒≱  ; n≤1+n)
open import Relation.Nullary using (yes ; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import AuxListTheory
open import Logic AtomicFormula
open import NaturalDeduction AtomicFormula

sm≤sn⇒m≤n : {m n : ℕ} → suc m ≤ suc n → m ≤ n 
sm≤sn⇒m≤n (s≤s p) = p

sn≤m⇒n≤m : {n m : ℕ} → suc n ≤ m → n ≤ m 
sn≤m⇒n≤m {n} p = ≤-trans (n≤1+n n) p

n≤k<m⇒φₖ∈[φ:n:m] : {m n k : ℕ} {φ : Formula} → n ≤ k → (suc k) ≤ m → φ at k ∈ time-range φ n m
n≤k<m⇒φₖ∈[φ:n:m] {zero} p ()
n≤k<m⇒φₖ∈[φ:n:m] {suc m} {n} {k} p (s≤s q) with n ≤? m
... | no q₁ = bot-elim (q₁ (≤-trans p q))
... | yes p₁ with (suc m) ≤? (suc k) 
...     | no q₂ = a∈l₁⇒a∈l₁++l₂ (n≤k<m⇒φₖ∈[φ:n:m] p (sm≤sn⇒m≤n (≰⇒> q₂)))
...     | yes (s≤s p₂) with ≤-antisym q p₂ 
...         | refl = a∈l₂⇒a∈l₁++l₂ {l₁ = time-range _ n m} ∈-here

Ax2 : (φ ψ : Formula) (n : ℕ) → [] ⊢ G (φ ⇒ ψ) ⇒ (G φ ⇒ G ψ) AT n
Ax2 φ ψ n = ⇒-intro (⇒-intro (
  G-intro (λ m p → ⇒-elim 
    (G-elim p (hyp (G (φ ⇒ ψ)) n {{∈-here}}))
    (G-elim p (hyp (G φ) n {{∈-there {{∈-here}}}})))
  ))

Ax3 : (φ : Formula) (n : ℕ) → [] ⊢ X (¬ φ) ⇔ ¬ (X φ) AT n
Ax3 φ n = ∧-intro
  (⇒-intro ( ⇒-intro (⊥-elim (⇒-elim
    (X-elim (hyp (X (¬ φ)) n {{∈-here}})) 
    (X-elim (hyp (X φ) n {{∈-there {{∈-here}}}}))
  ))))
  (⇒-intro (X-intro (⇒-intro (⊥-elim {m = n} (⇒-elim
    (hyp (¬ X φ) n {{∈-here}}) 
    (X-intro (hyp φ (suc n) {{∈-there {{∈-here}}}}))
  )))))

Ax4 : (φ ψ : Formula) (n : ℕ) → [] ⊢ X(φ ⇒ ψ) ⇒ (X φ ⇒ X ψ) AT n
Ax4 φ ψ n = ⇒-intro (⇒-intro (X-intro (⇒-elim
      (X-elim (hyp (X (φ ⇒ ψ)) n {{∈-here}}))
      (X-elim (hyp (X φ) n {{∈-there {{∈-here}}}}))
    )))

Ax5 : (φ : Formula) (n : ℕ) → [] ⊢ G φ ⇒ φ ∧ X G φ AT n
Ax5 φ n = ⇒-intro (∧-intro 
    (G-elim {n = n} {m = n} ≤-refl (hyp (G φ) n {{∈-here}})) 
    (X-intro (G-intro λ m sn≤m → G-elim {n = n} {m = m} 
      (sn≤m⇒n≤m sn≤m) (hyp (G φ) n {{∈-here}})))
  )

Ax6 : (φ : Formula) (n : ℕ) → [] ⊢ G (φ ⇒ X φ) ⇒ (φ ⇒ G φ) AT n 
Ax6 φ n = ⇒-intro (⇒-intro (G-intro λ m n≤m → aux φ n m n≤m)) where
  aux : (φ : Formula) (n m : ℕ) → n ≤ m → G (φ ⇒ X φ) at n ∷ [ φ at n ] ⊢ φ AT m 
  aux φ zero zero p = hyp φ zero {{∈-there {{∈-here}}}}
  aux φ n (suc m) p with (n ≤? m)
  ... | yes q = X-elim (⇒-elim (G-elim q (hyp (G (φ ⇒ X φ)) n {{∈-here}})) (aux φ n m q))
  ... | no q with ≤-antisym p (≰⇒> q)
  ...     | refl = hyp φ n {{∈-there {{∈-here}}}}

Ax7 : (φ ψ : Formula) (n : ℕ) → [] ⊢ φ U ψ ⇔ ψ ∨ φ ∧ X (φ U ψ) AT n
Ax7 φ ψ n = ∧-intro (⇒-intro (U-elim lemma₁ (hyp (φ U ψ) n {{∈-here}}))) (⇒-intro (lemma₂ n)) where 

      lemma₁ : (m : ℕ) → n ≤ m → φ U ψ at n ∷ time-range φ n m ++ [ ψ at m ] ⊢ ψ ∨ φ ∧ X (φ U ψ) AT n
      lemma₁ m p with (suc n) ≤? m
      ... | yes p₁ = ∨-intro₂ (∧-intro (hyp φ n {{aux₁}}) (X-intro (U-intro p₁ (hyp ψ m {{aux₂}}) aux₃))) 
        where 
          aux₁ : (φ at n) ∈ φ U ψ at n ∷ time-range φ n m ++ [ ψ at m ]
          aux₁ = ∈-there {{a∈l₁⇒a∈l₁++l₂ (n≤k<m⇒φₖ∈[φ:n:m] ≤-refl p₁)}}
          aux₂ : (ψ at m) ∈ φ U ψ at n ∷ time-range φ n m ++ ψ at m ∷ []
          aux₂ = a∈l₂⇒a∈l₁++l₂ {l₁ = [ φ U ψ at n ] ++ time-range φ n m} ∈-here
          aux₃ : (k : ℕ) → suc n ≤ k → k < m → φ U ψ at n ∷ time-range φ n m ++ ψ at m ∷ [] ⊢ φ AT k
          aux₃ k q₁ q₂ = hyp φ k {{∈-there {{a∈l₁⇒a∈l₁++l₂ (n≤k<m⇒φₖ∈[φ:n:m] (sn≤m⇒n≤m q₁) q₂)}}}}  
      ... | no q₁ with ≤-antisym p (sm≤sn⇒m≤n (≰⇒> q₁))
      ...     | refl = ∨-intro₁ (hyp ψ n {{a∈l₂⇒a∈l₁++l₂ {l₁ = [ φ U ψ at n ] ++ time-range φ n m} ∈-here}})

      lemma₂ : (n : ℕ) → [ (ψ ∨ φ ∧ X (φ U ψ)) at n ] ⊢ φ U ψ AT n
      lemma₂ n = ∨-elim (hyp _ _ {{∈-here}})
        (U-intro ≤-refl (hyp ψ n {{∈-there {{∈-here}}}}) (λ k q₁ q₂ → bot-elim (<⇒≱  q₂ q₁)))
        (weaken {Δ₁ = []} (ψ ∨ φ ∧ X (φ U ψ)) (U-elim
          (λ m q → U-intro (sn≤m⇒n≤m q)
            (hyp ψ m {{a∈l₂⇒a∈l₁++l₂ {l₁ = (φ ∧ X φ U ψ) at n ∷ time-range φ (suc n) m} ∈-here}}) (aux m))
          (X-elim (∧-elim₂ (hyp _ _ {{∈-here}})))
        )) where 
          aux : (m k : ℕ) → n ≤ k → k < m → (φ ∧ X φ U ψ) at n ∷ time-range φ (suc n) m ++ [ ψ at m ] ⊢ φ AT k
          aux m k q₁ q₂ with k ≤? n  
          ... | no p₂ = hyp φ k {{∈-there {{a∈l₁⇒a∈l₁++l₂ (n≤k<m⇒φₖ∈[φ:n:m] (≰⇒> p₂) q₂)}}}}
          ... | yes p₁ with ≤-antisym p₁ q₁
          ...     | refl = ∧-elim₁ (hyp _ _ {{∈-here}})

Ax8 : (φ ψ : Formula) (n : ℕ) → [] ⊢ φ U ψ ⇒ F ψ AT n
Ax8 φ ψ n = ⇒-intro (⇒-intro (U-elim 
    (λ m p → ⊥-elim (⇒-elim 
      (G-elim p (hyp _ _ {{∈-there {{∈-here}}}})) 
      (hyp _ _ {{∈-there {{∈-there {{a∈l₂⇒a∈l₁++l₂ ∈-here}}}}}})
    )) 
    (hyp _ _ {{∈-here}})
  ))