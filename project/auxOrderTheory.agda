module auxOrderTheory where

open import Data.Nat using (ℕ ; zero ; suc ; _≤_ ; _<_ ; z≤n ; s≤s)
open import Data.Empty renaming (⊥-elim to bot-elim)
open import Relation.Nullary renaming (¬_ to neg_)


sm≤sn⇒m≤n : {m n : ℕ} → suc m ≤ suc n → m ≤ n 
sm≤sn⇒m≤n (s≤s p) = p

sn≤m⇒n≤m : {n m : ℕ} → suc n ≤ m → n ≤ m 
sn≤m⇒n≤m {zero} p = z≤n
sn≤m⇒n≤m {suc n} (s≤s p) = s≤s (sn≤m⇒n≤m p)

m<n∧n≤m⇒⊥ : {m n : ℕ} → m < n → n ≤ m → ⊥
m<n∧n≤m⇒⊥ (s≤s (s≤s (s≤s z≤n))) (s≤s (s≤s ()))
m<n∧n≤m⇒⊥ (s≤s (s≤s (s≤s (s≤s p)))) (s≤s q) = m<n∧n≤m⇒⊥ q (s≤s (s≤s p))

m≤n∧¬m≤n⇒⊥ : {m n : ℕ} → m ≤ n → neg m ≤ n → ⊥
m≤n∧¬m≤n⇒⊥ z≤n q = q z≤n
m≤n∧¬m≤n⇒⊥ {m = (suc m)} {n = (suc n)} (s≤s p) q = m≤n∧¬m≤n⇒⊥ p (aux q) where 
     aux : (neg suc m ≤ suc n) → neg m ≤ n
     aux x r = x (s≤s r) 