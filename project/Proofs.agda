open import Data.Nat using (ℕ ; zero ; suc ; _≤_ ; _<_ ; z≤n ; s≤s)
open import HProp

module Proofs (AtomicFormula : Set) where

open import Data.List using (List ; [] ; [_] ; _∷_ ; _++_)
open import Data.List.Properties using (++-assoc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import Data.Nat.Properties using (_≤?_)
open import Relation.Nullary using (yes ; no)

open import auxOrderTheory
open import auxListTheory
open import Logic AtomicFormula
open import NaturalDeduction AtomicFormula


n≤k<m⇒φₖ∈[φ:n:m] : {m n k : ℕ} {φ : Formula} → n ≤ k → (suc k) ≤ m → (φ at k) ∈ (time-range φ n m)
n≤k<m⇒φₖ∈[φ:n:m] {zero} {n} {k} p ()
n≤k<m⇒φₖ∈[φ:n:m] {suc m} {n} {k} p (s≤s q) with n ≤? m
... | no q₁ = ⊥⇒⋆ {m = m} {n = n} (m≤n∧¬m≤n⇒⊥ (k≤m∧m≤n⇒k≤n p q) q₁)
... | yes p₁ with (suc m) ≤? (suc k) 
...     | no q₂ = ∈-there {{n≤k<m⇒φₖ∈[φ:n:m] p (sm≤sn⇒m≤n (¬m≤n⇒m>n q₂))}}
...     | yes (s≤s p₂) with m≤n∧n≤m⇒m≡n q p₂ 
...         | refl = ∈-here

Ax2 : (φ ψ : Formula) (n : ℕ) → [] ⊢ G (φ ⇒ ψ) ⇒ (G φ ⇒ G ψ) AT n
Ax2 φ ψ n = ⇒-intro (⇒-intro (
  G-intro (λ m p → ⇒-elim {φ = φ} 
    (G-elim p (hyp (G (φ ⇒ ψ)) n {{∈-here}}))
    (G-elim p (hyp (G φ) n {{∈-there {{∈-here}}}})))
  ))

Ax3 : (φ : Formula) (n : ℕ) → [] ⊢ X (¬ φ) ⇔ ¬ (X φ) AT n
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
    (G-elim {n = n} {m = n} n≤n (hyp (G φ) n {{∈-here}})) 
    (X-intro (G-intro λ m sn≤m → G-elim {n = n} {m = m} 
      (sn≤m⇒n≤m sn≤m) (hyp (G φ) n {{∈-here}})))
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

Ax7 : (φ ψ : Formula) (n : ℕ) → [] ⊢ φ U ψ ⇔ ψ ∨ φ ∧ X (φ U ψ) AT n
Ax7 φ ψ n = ∧-intro 
  (⇒-intro (U-elim lemma₁ (hyp (φ U ψ) n {{∈-here}}))) 
  (⇒-intro (lemma₂ n)) 
    where 
    
      lemma₁ : (m : ℕ) → n ≤ m → φ U ψ at n ∷ time-range φ n m ++ [ ψ at m ] ⊢ ψ ∨ φ ∧ X (φ U ψ) AT n
      lemma₁ m p with (suc n) ≤? m
      ... | yes p₁ = ∨-intro₂ (∧-intro 
          (hyp φ n {{∈-there {{aux₁}}}}) 
          (X-intro (U-intro p₁ (hyp ψ m {{aux₂}}) aux₃))
        ) 
        where 
          aux₁ : (φ at n) ∈ (time-range φ n m) ++ [ ψ at m ]
          aux₁ = a∈l₁⇒a∈l₁++l₂ (n≤k<m⇒φₖ∈[φ:n:m] n≤n p₁)
          aux₂ : (ψ at m) ∈ φ U ψ at n ∷ time-range φ n m ++ ψ at m ∷ []
          aux₂ = a∈l₂⇒a∈l₁++l₂ {l₁ = φ U ψ at n ∷ time-range φ n m} ∈-here
          aux₃ : (k : ℕ) → suc n ≤ k → k < m → φ U ψ at n ∷ time-range φ n m ++ ψ at m ∷ [] ⊢ φ AT k
          aux₃ k q₁ q₂ = hyp φ k {{∈-there {{a∈l₁⇒a∈l₁++l₂ (n≤k<m⇒φₖ∈[φ:n:m] (sn≤m⇒n≤m q₁) q₂)}}}}  
      ... | no q₁ with m≤n∧n≤m⇒m≡n p (sm≤sn⇒m≤n (¬m≤n⇒m>n q₁))
      ...     | refl = ∨-intro₁ (hyp ψ n {{a∈l₂⇒a∈l₁++l₂ {l₁ = [ φ U ψ at n ] ++ time-range φ n m} ∈-here}})

      lemma₂ : (n : ℕ) → [ (ψ ∨ φ ∧ X (φ U ψ)) at n ] ⊢ φ U ψ AT n
      lemma₂ n = ∨-elim {φ₁ = ψ} {φ₂ = φ ∧ X φ U ψ} (hyp _ _ {{∈-here}})
        (U-intro n≤n (hyp ψ n {{∈-there {{∈-here}}}}) (λ k q₁ q₂ → ⊥⇒⋆ {m = k} {n = n} (m<n∧n≤m⇒⊥ q₂ q₁)))
        (weaken {Δ₁ = []} (ψ ∨ φ ∧ X (φ U ψ)) (aux n))
        where 
          aux : (n : ℕ) → [ (φ ∧ X φ U ψ) at n ] ⊢ φ U ψ AT n
          aux n = U-elim {n = suc n} 
            (λ m q → U-intro (sn≤m⇒n≤m q)
              (hyp ψ m {{a∈l₂⇒a∈l₁++l₂ {l₁ = (φ ∧ X φ U ψ) at n ∷ time-range φ (suc n) m} ∈-here}}) (aux' m)) 
            (X-elim (∧-elim₂ (hyp _ _ {{∈-here}}))) where 
              aux' : (m k : ℕ) → n ≤ k → k < m → (φ ∧ X φ U ψ) at n ∷ time-range φ (suc n) m ++ [ ψ at m ] ⊢ φ AT k
              aux' m k q₁ q₂ with k ≤? n  
              ... | no p₂ = hyp φ k {{∈-there {{a∈l₁⇒a∈l₁++l₂ {l₁ = time-range φ (suc n) m}
                (n≤k<m⇒φₖ∈[φ:n:m] {m = m} {n = suc n} (¬m≤n⇒m>n p₂) q₂)}}}}
              ... | yes p₁ with m≤n∧n≤m⇒m≡n p₁ q₁
              ...     | refl = ∧-elim₁ (hyp _ _ {{∈-here}})

Ax8 : (φ ψ : Formula) (n : ℕ) → [] ⊢ φ U ψ ⇒ F ψ AT n
Ax8 φ ψ n = ⇒-intro (⇒-intro (U-elim 
    (λ m p → ⊥-elim {m = m} (⇒-elim 
      (G-elim p (hyp _ _ {{∈-there {{∈-here}}}})) 
      (hyp _ _ {{∈-there {{∈-there {{a∈l₂⇒a∈l₁++l₂ {l₁ = time-range φ n m} ∈-here}}}}}})
    )) 
    (hyp _ _ {{∈-here}})
  ))