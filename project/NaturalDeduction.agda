module NaturalDeduction (AtomicFormula : Set) where

open import Data.Nat using (ℕ ; zero ; suc ; _≤_ ; z≤n ; s≤s ; _<_)
open import Data.List using (List ; [] ; _∷_ ; [_] ; _++_)
open import Data.Sum using (_⊎_)
open import Data.Nat.Properties using (_≤?_)
open import Relation.Binary.PropositionalEquality using (refl)
open import Relation.Nullary renaming (¬_ to neg_)

open import AuxListTheory using (_∈_)
open import Logic AtomicFormula

record TimeFormula : Set where
  constructor _at_
  field
    formula : Formula
    time : ℕ

open TimeFormula public
infixr 19 _at_

Hypotheses = List TimeFormula

-- [φ at n, φ at n+1, ..., φ at m-1]
time-range : (φ : Formula) (n m : ℕ) → Hypotheses 
time-range φ n zero = []
time-range φ n (suc m) with n ≤? m
... | yes _ =  time-range φ n m ++ [ φ at m ]
... | no _ = []

infixl 1 _⊢_AT_
data _⊢_AT_ : (Δ : Hypotheses) → (φ : Formula) → (n : ℕ) → Set where

  weaken : {Δ₁ Δ₂ : Hypotheses}
    → (φ : Formula)
    → {ψ : Formula}
    → {n : ℕ}
    → Δ₁ ++ Δ₂ ⊢ ψ AT n
    ---------------------------------
    → Δ₁ ++ [ φ at n ] ++ Δ₂ ⊢ ψ AT n


  contract : {Δ₁ Δ₂ : Hypotheses}
    → (φ : Formula)
    → {ψ : Formula}
    → {n : ℕ}
    → Δ₁ ++ [ φ at n ] ++ [ φ at n ] ++ Δ₂ ⊢ ψ AT n
    -----------------------------------------------
    → Δ₁ ++ [ φ at n ] ++ Δ₂ ⊢ ψ AT n

  exchange : {Δ₁ Δ₂ : Hypotheses}
    → (φ₁ φ₂ : Formula)
    → {ψ : Formula}
    → {m n : ℕ}
    → Δ₁ ++ [ φ₁ at m ] ++ [ φ₂ at n ] ++ Δ₂ ⊢ ψ AT n
    --------------------------------------------------
    → Δ₁ ++ [ φ₂ at n ] ++ [ φ₁ at m ] ++ Δ₂ ⊢ ψ AT n

  -- hypotheses

  hyp : {Δ : Hypotheses}
    → (φ : Formula)
    → (n : ℕ)
    → {{φ at n ∈ Δ}}
    ----------------
    → Δ ⊢ φ AT n

  -- propositional logic

  ⊥-elim : {Δ : Hypotheses}
    → {φ : Formula}
    → {n m : ℕ}
    → Δ ⊢ ⊥ AT m
    -------------
    → Δ ⊢ φ AT n 
  
  ⊤-intro : {Δ : Hypotheses}
    → {n : ℕ}
    -------------
    → Δ ⊢ ⊤ AT n

  ∧-intro : {Δ : Hypotheses}
    → {φ ψ : Formula}
    → {n : ℕ}
    → Δ ⊢ φ AT n
    → Δ ⊢ ψ AT n
    -----------------
    → Δ ⊢ φ ∧ ψ AT n

  ∧-elim₁ : {Δ : Hypotheses}
    → {φ ψ : Formula}
    → {n : ℕ}
    → Δ ⊢ φ ∧ ψ AT n
    ----------------
    → Δ ⊢ φ AT n

  ∧-elim₂ : {Δ : Hypotheses}
    → {φ ψ : Formula}
    → {n : ℕ}
    → Δ ⊢ φ ∧ ψ AT n
    ----------------
    → Δ ⊢ ψ AT n

  ∨-intro₁ : {Δ : Hypotheses}
    → {φ ψ : Formula}
    → {n : ℕ}
    → Δ ⊢ φ AT n
    -----------------
    → Δ ⊢ φ ∨ ψ AT n

  ∨-intro₂ : {Δ : Hypotheses}
    → {φ ψ : Formula}
    → {n : ℕ}
    → Δ ⊢ ψ AT n
    -----------------
    → Δ ⊢ φ ∨ ψ AT n

  ∨-elim : {Δ : Hypotheses}
    → {φ₁ φ₂ ψ : Formula}
    → {n : ℕ}
    → Δ ⊢ φ₁ ∨ φ₂ AT n
    → Δ ++ [ φ₁ at n ] ⊢ ψ AT n
    → Δ ++ [ φ₂ at n ] ⊢ ψ AT n
    ---------------------------
    → Δ ⊢ ψ AT n

  ⇒-intro : {Δ : Hypotheses}
    → {φ ψ : Formula}
    → {n : ℕ}
    → Δ ++ [ φ at n ] ⊢ ψ AT n
    --------------------------
    → Δ ⊢ (φ ⇒ ψ) AT n

  ⇒-elim : {Δ : Hypotheses}
    → {φ ψ : Formula}
    → {n : ℕ}
    → Δ ⊢ (φ ⇒ ψ) AT n
    → Δ ⊢ φ AT n 
    -------------
    → Δ ⊢ ψ AT n

  -- temporal logic

  X-intro : {Δ : Hypotheses}
    → {φ : Formula}
    → {n : ℕ}
    → Δ ⊢ φ AT (suc n)
    ------------------
    → Δ ⊢ (X φ) AT n

  X-elim : {Δ : Hypotheses}
    → {φ : Formula}
    → {n : ℕ}
    → Δ ⊢ X φ AT n
    ------------------
    → Δ ⊢ φ AT (suc n)
  
  G-intro : {Δ : Hypotheses}
    → {φ : Formula}
    → {n : ℕ}
    → ((m : ℕ) → n ≤ m → Δ ⊢ φ AT m)
    --------------------------------
    → Δ ⊢ G φ AT n

  G-elim : {Δ : Hypotheses}
    → {φ : Formula}
    → {n m : ℕ}
    → n ≤ m
    → Δ ⊢ G φ AT n
    -------------
    → Δ ⊢ φ AT m
  
  U-intro : {Δ : Hypotheses} 
    → {φ ψ : Formula}
    → {n m : ℕ} 
    → n ≤ m
    → Δ ⊢ ψ AT m
    → ((k : ℕ) → n ≤ k → k < m → Δ ⊢ φ AT k)
    ----------------------------------------
    → Δ ⊢ φ U ψ AT n

  U-elim : {Δ : Hypotheses}
    → {φ ψ ρ : Formula}
    → {n k : ℕ} 
    → ((m : ℕ) → (n ≤ m) → Δ ++ (time-range φ n m) ++ [ ψ at m ] ⊢ ρ AT k)
    → Δ ⊢ φ U ψ AT n
    ----------------
    → Δ ⊢ ρ AT k