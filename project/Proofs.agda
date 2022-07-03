open import Data.Nat using (ℕ ; zero ; suc ; _≤_ ; _<_ ; z≤n ; s≤s)
open import HProp

module Proofs (AtomicFormula : Set) where

open import Data.List using (List ; [] ; [_] ; _∷_ ; _++_)
open import Data.List.Properties using (++-assoc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import Data.Nat.Properties using (_≤?_)
open import Relation.Nullary using (yes ; no)

open import AdvancedNumberTheory
open import AdvancedListTheory

open import Logic AtomicFormula
open import NaturalDeduction AtomicFormula


n≤k<m⇒φₖ∈[φ:n:m] : {m n k : ℕ} {φ : Formula} → n ≤ k → (suc k) ≤ m → (φ at k) ∈ (time-range φ n m)
n≤k<m⇒φₖ∈[φ:n:m] {zero} {n} {k} p ()
n≤k<m⇒φₖ∈[φ:n:m] {suc m} {n} {k} p (s≤s q) with n ≤? m
... | no q₁ = m≤n∧¬m≤n⇒⋆ (k≤m∧m≤n⇒k≤n p q) q₁
... | yes p₁ with (suc m) ≤? (suc k) 
...     | no q₂ = ∈-there {{n≤k<m⇒φₖ∈[φ:n:m] p (sm≤sn⇒m≤n (¬m≤n⇒m>n q₂))}}
...     | yes (s≤s p₂) with m≤n∧n≤m⇒m≡n q p₂ 
...         | refl = ∈-here

n<m⇒φₙ∈[φ∶n∶m] : {m n : ℕ} {φ : Formula} → suc n ≤ m → (φ at n) ∈ (time-range φ n m)
n<m⇒φₙ∈[φ∶n∶m] p = n≤k<m⇒φₖ∈[φ:n:m] n≤n p

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

Ax7' : (φ ψ : Formula) (n : ℕ) → [] ⊢ φ U ψ ⇔ ψ ∨ φ ∧ X (φ U ψ) AT n
Ax7' φ ψ n = ∧-intro 
  (⇒-intro (U-elim lemma₁ (hyp (φ U ψ) n {{∈-here}}))) 
  (⇒-intro (lemma₂ n)) 
    where 
    
      lemma₁ : (m : ℕ) → n ≤ m → φ U ψ at n ∷ time-range φ n m ++ [ ψ at m ] ⊢ ψ ∨ φ ∧ X (φ U ψ) AT n
      lemma₁ m p with (suc n) ≤? m
      ... | yes p₁ = ∨-intro₂ (∧-intro (hyp φ n {{∈-there {{aux₂}}}}) (X-intro (U-intro p₁ (hyp ψ m {{aux₃}}) aux₄))) 
        where 
          aux₁ : (φ at n) ∈ (time-range φ n m) 
          aux₁ = n<m⇒φₙ∈[φ∶n∶m] {m = m} p₁
          aux₂ : (φ at n) ∈ (time-range φ n m) ++ [ ψ at m ]
          aux₂ = a∈l₁⇒a∈l₁++l₂ aux₁
          aux₃ : (ψ at m) ∈ φ U ψ at n ∷ time-range φ n m ++ ψ at m ∷ []
          aux₃ = a∈l₂⇒a∈l₁++l₂ {l₁ = φ U ψ at n ∷ time-range φ n m} ∈-here
          aux₄ : (k : ℕ) → suc n ≤ k → k < m → φ U ψ at n ∷ time-range φ n m ++ ψ at m ∷ [] ⊢ φ AT k
          aux₄ k q₁ q₂ = hyp φ k {{∈-there {{a∈l₁⇒a∈l₁++l₂ (n≤k<m⇒φₖ∈[φ:n:m] (sn≤m⇒n≤m q₁) q₂)}}}}  
      ... | no q₁ with m≤n∧n≤m⇒m≡n p (sm≤sn⇒m≤n (¬m≤n⇒m>n q₁))
      ...     | refl = ∨-intro₁ (hyp ψ n {{a∈l₂⇒a∈l₁++l₂ {l₁ = [ φ U ψ at n ] ++ time-range φ n m} ∈-here}})

      lemma₂ : (n : ℕ) → [ (ψ ∨ φ ∧ X (φ U ψ)) at n ] ⊢ φ U ψ AT n
      lemma₂ n = ∨-elim {φ₁ = ψ} {φ₂ = φ ∧ X φ U ψ} (hyp _ _ {{∈-here}})
        (U-intro n≤n (hyp ψ n {{∈-there {{∈-here}}}}) (λ k q₁ q₂ → m<n∧n≤m⇒⋆ q₂ q₁))
        (weaken {Δ₁ = []} (ψ ∨ φ ∧ X (φ U ψ)) (aux n)) 
        where 
          aux : (n : ℕ) → [ (φ ∧ X φ U ψ) at n ] ⊢ φ U ψ AT n
          aux n = U-elim {n = suc n} 
            (λ m q → U-intro (sn≤m⇒n≤m q) 
              (hyp ψ m {{a∈l₂⇒a∈l₁++l₂ {l₁ = (φ ∧ X φ U ψ) at n ∷ time-range φ (suc n) m} ∈-here}}) 
              (aux' m)) 
            (X-elim (∧-elim₂ (hyp _ _ {{∈-here}}))) where 
              aux' : (m k : ℕ) → n ≤ k → k < m → (φ ∧ X φ U ψ) at n ∷ time-range φ (suc n) m ++ [ ψ at m ] ⊢ φ AT k
              aux' m k q₁ q₂ with k ≤? n  
              ... | no p₂ = hyp φ k {{∈-there {{a∈l₁⇒a∈l₁++l₂ {l₁ = time-range φ (suc n) m} 
                (n≤k<m⇒φₖ∈[φ:n:m] {m = m} {n = suc n} (¬m≤n⇒m>n p₂) q₂)}}}}
              ... | yes p₁ with m≤n∧n≤m⇒m≡n p₁ q₁
              ...     | refl = ∧-elim₁ (hyp _ _ {{∈-here}})

Ax8 : (φ ψ : Formula) (n : ℕ) → [] ⊢ φ U ψ ⇒ F ψ AT n
Ax8 φ ψ n = ⇒-intro (⇒-intro {!!})

{- 
Lemma1 : (φ : Formula) (n m : ℕ) → suc n ≤ m →
       time-range φ n m ⊢ φ AT n
Lemma1 φ n m (s≤s z≤n) = hyp φ zero {{n<m⇒φₙ∈[φ∶n∶m] (s≤s z≤n)}}
Lemma1 φ n m (s≤s (s≤s x)) = hyp φ n {{n<m⇒φₙ∈[φ∶n∶m] (s≤s (s≤s x))}}

Ax7 : (φ ψ : Formula) (n : ℕ) → [] ⊢ φ U ψ ⇔ ψ ∨ (φ ∧ X (φ U ψ)) AT n
Ax7 φ ψ n = ∧-intro
  (⇒-intro (U-elim
    (λ { zero (z≤n {zero}) → ∨-intro₁ (hyp ψ zero {{∈-there}}) ;
         (suc m) (z≤n {suc m}) → ∨-intro₂ (∧-intro (weaken (φ U ψ) (weaken φ (weaken ψ (Lemma1 φ zero (suc m) (s≤s z≤n)))))
              (X-intro (U-intro (s≤s z≤n) (hyp ψ (suc m) {{{!!}}}) (λ k p q → weaken (φ U ψ) (weaken φ (weaken ψ (hyp φ k))))))) ; -- Zakaj ne prepozna da ψ at suc m ∈ Δ ++ [ ψ at suc m ]?
         m (s≤s x) → ∨-intro₂ (∧-intro {!!} {!!})} ) 
    (hyp (φ U ψ) n)))
  {!!}

--Niti ni koristna funkcija trenutno ampak morda bo
Mogoc : (φ : Formula) (n : ℕ) → φ at n ∷ [ (¬ φ) at n ] ⊢ ⊥ AT n
Mogoc φ n = ⇒-elim (hyp (¬ φ) n) (hyp φ n)
-}
 