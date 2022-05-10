open import HProp

module Tautologies (AtomicFormula : Set) (η : AtomicFormula → HProp)  where

open import Data.Nat using (ℕ)
open import Data.Product

open import Logic AtomicFormula
open import Semantics AtomicFormula η

-- stran 32 na https://www.math.tecnico.ulisboa.pt/~mvolpe/publications/theses/volpe-phd-thesis.pdf

Axiom8 : (A B : Formula) (n : ℕ) →  proof(⟦ (A U B) ⇒ (F B) ⟧ n)
Axiom8 A B n p = ∥∥-elim (is-prop(⟦ F B ⟧ n)) (λ (k , r) q → q k (proj₁ r) (proj₁ (proj₂ r))) p

-- Need to find a inhabitant of proof() 
-- which is a function from proof (A U B) to proof (F B)
-- p is the proof (A U B), we use ∥∥-elim to unwrap (F B) 

Axiom2 : (A B : Formula) (n : ℕ) → proof(⟦ G (A ⇒ B) ⇒ (G A ⇒ G B)⟧ n)
Axiom2 A B n p = λ q k n≤k → p k n≤k (q k n≤k) -- c-c c-a

Axiom3 : (A : Formula) (n : ℕ) → proof(⟦ X (¬ A) ⇔ ¬ (X A) ⟧ n)
Axiom3 A n = (λ x → x) , (λ x → x) -- c-c c-a

Axiom4 : (A B : Formula) (n : ℕ) → proof(⟦ X(A ⇒ B) ⇒ (X A ⇒ X B) ⟧ n)
Axiom4 A B n p q = p q

Axiom5 : (A : Formula) (n : ℕ) → proof(⟦ G A ⇒ A ∧ X G A ⟧ n)
Axiom5 A n x = {!!}

-- Eksperimentacija s pojmi, da razumema

c = ⟦ G (⊤ ⇒ ⊤) ⇒ (G ⊤ ⇒ G ⊤)⟧ 5
d = ⟦ ⊤ ⇒ Formula.⊥ ⟧ 3
 
-- Natural deduction but first a proof system without Until


open import Data.List  using (List; []; _∷_; [_]; _++_) public
Hypotheses = List (Formula)

infixl 2 _⊢_

data _⊢_ : (Δ : Hypotheses) → (φ : Formula) → Set where    -- unicode \vdash


  weaken   : {Δ₁ Δ₂ : Hypotheses}
                → (φ : Formula)
                → {ψ : Formula}
                → Δ₁ ++ Δ₂ ⊢ ψ
                -----------------------
                → Δ₁ ++ [ φ ] ++ Δ₂ ⊢ ψ


--⊥E    :   {A : Formula} {n : ℕ} →
--        →  
