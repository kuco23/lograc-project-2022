module AdvancedNumberTheory where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Data.Nat using (ℕ ; zero ; suc ; _≤_ ; _<_ ; z≤n ; s≤s)
open import Data.Nat.Properties using (_≤?_)
open import Data.Empty renaming (⊥-elim to neg-elim)
open import Relation.Nullary renaming (¬_ to neg_)

n≤n : {n : ℕ} → n ≤ n 
n≤n {zero} = z≤n
n≤n {suc n} = s≤s (n≤n {n})

sm≤sn⇒m≤n : {m n : ℕ} → suc m ≤ suc n → m ≤ n 
sm≤sn⇒m≤n (s≤s p) = p

¬sn≤sm⇒¬n≤m : {n m : ℕ} → neg (suc n ≤ suc m) → neg n ≤ m
¬sn≤sm⇒¬n≤m p = λ z → p (s≤s z)

m≤n⇒m≤sn : {m n : ℕ} → m ≤ n → m ≤ suc n 
m≤n⇒m≤sn {.zero} {n} z≤n = z≤n
m≤n⇒m≤sn {.(suc _)} {.(suc _)} (s≤s p) = s≤s (m≤n⇒m≤sn {_} {_} p)

sn≤m⇒n≤m : {n m : ℕ} → suc n ≤ m → n ≤ m 
sn≤m⇒n≤m {zero} p = z≤n
sn≤m⇒n≤m {suc n} (s≤s p) = s≤s (sn≤m⇒n≤m p)

n≤sm∧¬n≤m⇒n≡sm : {n m : ℕ} → (n ≤ suc m) → (neg n ≤ m) → n ≡ (suc m)
n≤sm∧¬n≤m⇒n≡sm {zero} {zero} z≤n q = neg-elim (q z≤n)
n≤sm∧¬n≤m⇒n≡sm {suc n} {zero} (s≤s p) q = cong suc (aux p) where
  aux : (n ≤ zero) → n ≡ zero
  aux z≤n = refl
n≤sm∧¬n≤m⇒n≡sm {zero} {suc m} z≤n q = neg-elim (q z≤n)
n≤sm∧¬n≤m⇒n≡sm {suc n} {suc m} (s≤s p) q = cong suc (n≤sm∧¬n≤m⇒n≡sm {n} {m} p (aux q)) where
  aux : (neg suc n ≤ suc m) → neg n ≤ m
  aux x r = x (s≤s r)

k≤m∧m≤n⇒k≤n : {k m n : ℕ} → k ≤ m → m ≤ n → k ≤ n 
k≤m∧m≤n⇒k≤n {zero} p q = z≤n
k≤m∧m≤n⇒k≤n {suc k} (s≤s p) (s≤s q) = s≤s (k≤m∧m≤n⇒k≤n p q)

m≤n∧n≤m⇒m≡n : {m n : ℕ} → m ≤ n → n ≤ m → m ≡ n 
m≤n∧n≤m⇒m≡n {zero} p z≤n = refl
m≤n∧n≤m⇒m≡n {suc m} {zero} () q
m≤n∧n≤m⇒m≡n {suc m} {suc n} (s≤s p) (s≤s q) = cong suc (m≤n∧n≤m⇒m≡n p q)

postulate ¬m≤n⇒m>n : {m n : ℕ} → neg m ≤ n → suc n ≤ m 
postulate m>n⇒¬m≤n : {m n : ℕ} → suc n ≤ m → neg m ≤ n

m≤n∧¬m≤n⇒⋆ : {A : Set} {m n : ℕ} → m ≤ n → neg m ≤ n → A 
m≤n∧¬m≤n⇒⋆ z≤n q with q z≤n
... | ()
m≤n∧¬m≤n⇒⋆ {m = (suc m)} {n = (suc n)} (s≤s p) q = m≤n∧¬m≤n⇒⋆ p (aux q) where 
     aux : (neg suc m ≤ suc n) → neg m ≤ n
     aux x r = x (s≤s r)
     
m<n∧n≤m⇒⋆ : {A : Set} {m n : ℕ} → m < n → n ≤ m → A 
m<n∧n≤m⇒⋆ p q = m≤n∧¬m≤n⇒⋆ q (m>n⇒¬m≤n p)