module NaturalDeduction (AtomicFormula : Set) where

import Data.List  using (List; []; _∷_; [_]; _++_)
open Data.List
open import Logic AtomicFormula

open import Data.Nat using (ℕ ; suc ; _≤_) -- Perhaps useful for time
open import Data.Sum using (_⊎_) -- Maybe necessary for the future


record TimeFormula : Set where
  constructor _at_
  field
    formula : Formula
    time : ℕ

open TimeFormula public
infixr 19 _at_

Hypotheses = List (TimeFormula)

infix 3 _∈_
data _∈_ {A : Set} : A → List A → Set where
  instance
    ∈-here  : {x : A} → {xs : List A} → x ∈ (x ∷ xs)
    ∈-there : {x y : A} {xs : List A} → {{x ∈ xs}} → x ∈ (y ∷ xs)

infixl 1 _⊢_AT_
data _⊢_AT_  : (Δ : Hypotheses) → (φ : Formula) → (n : ℕ) → Set where    -- unicode \vdash

      -- structural rules

     weaken   : {Δ₁ Δ₂ : Hypotheses}
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
           ---------------------------------
           → Δ₁ ++ [ φ at n ] ++ Δ₂ ⊢ ψ AT n

     exchange : {Δ₁ Δ₂ : Hypotheses}
           → (φ₁ φ₂ : Formula)
           → {ψ : Formula}
           → {n : ℕ}
           → Δ₁ ++ [ φ₁ at n ] ++ [ φ₂ at n ] ++ Δ₂ ⊢ ψ AT n
           --------------------------------------------------
           → Δ₁ ++ [ φ₂ at n ] ++ [ φ₁ at n ] ++ Δ₂ ⊢ ψ AT n

  -- hypotheses

     hyp      : {Δ : Hypotheses}
           → (φ : Formula)
           → (n : ℕ)
           → {{φ at n ∈ Δ}}
           -------------
           → Δ ⊢ φ AT n

  -- simple temporal rules
  -- https://www.math.tecnico.ulisboa.pt/~mvolpe/publications/theses/volpe-phd-thesis.pdf page 78
  
     ⊥-elim   : {Δ : Hypotheses}
          → {A : Formula}
          → {n m : ℕ}
          → Δ ++ [ (¬ A) at n ] ⊢ ⊥ AT m
          -------------
          → Δ ⊢ A AT n 

     ⇒-intro : {Δ : Hypotheses}
          → {A B : Formula}
          → {n : ℕ}
          → Δ ++ [ A at n ] ⊢ B AT n
          -------------------
          → Δ ⊢ (A ⇒ B) AT n

     ⇒-elim : {Δ : Hypotheses}
          → {A B : Formula}
          → {n : ℕ}
          → Δ ⊢ (A ⇒ B) AT n
          → Δ ⊢ A AT n 
          -------------
          → Δ ⊢ B AT n

     X-intro : {Δ : Hypotheses}
          → {A : Formula}
          → {n : ℕ}
          → Δ ⊢ A AT (suc n)
          -----------------
          → Δ ⊢ (X A) AT n

     X-elim : {Δ : Hypotheses}
          → {A : Formula}
          → {n : ℕ}
          → Δ ⊢ X A AT n
          ------------------
          → Δ ⊢ A AT (suc n)

     {-ser◂ : {Δ : Hypotheses} -- ◂ is written like \t
          → {A B : Formula}    -- Perhaps not necessary to write down here
          → {n m : ℕ}             -- since our code works different from page
          → Δ ++  ⊢ A AT m   -- 70 of the doctorate thesis
          -------------
          → Δ ⊢ A AT m -}

     -- also lin◂ is ignored for now
     
     G-intro : {Δ : Hypotheses}
          → {A : Formula}
          → {n : ℕ}
          → ((m : ℕ) → n ≤ m → Δ ⊢ A AT m)
          ---------------
          → Δ ⊢ G A AT n

     G-elim : {Δ : Hypotheses}
          → {A : Formula}
          → {n m : ℕ}
          → Δ ⊢ G A AT n
          → n ≤ m
          -------------
          → Δ ⊢ A AT m

  -- Probably dont need refl≤

  -- also not trans≤

  -- also not base≤

 -- Classical Logic Things

     ⊤-intro  : {Δ : Hypotheses}
                   {n : ℕ}
           ------------------
           → Δ ⊢ ⊤ AT n


     -- conjunction

     ∧-intro  : {Δ : Hypotheses}
              → {A B : Formula}
              → {n : ℕ}
              → Δ ⊢ A AT n
              → Δ ⊢ B AT n
              -------------------
              → Δ ⊢ A ∧ B AT n

     ∧-elim₁  : {Δ : Hypotheses}
              → {A B : Formula}
              → {n : ℕ}
              → Δ ⊢ A ∧ B AT n
              -------------------
              → Δ ⊢ A AT n

     ∧-elim₂  : {Δ : Hypotheses}
              → {A B : Formula}
              → {n : ℕ}
              → Δ ⊢ A ∧ B AT n
              -------------------
              → Δ ⊢ B AT n

     -- disjunction

     ∨-intro₁ : {Δ : Hypotheses}
              → {A B : Formula}
              → {n : ℕ}
              → Δ ⊢ A AT n
              ------------------
              → Δ ⊢ A ∨ B AT n

     ∨-intro₂ : {Δ : Hypotheses}
              → {A B : Formula}
              → {n : ℕ}
              → Δ ⊢ B AT n
              -------------------
              → Δ ⊢ A ∨ B AT n

     ∨-elim   : {Δ : Hypotheses}
              → {A₁ A₂ B : Formula}
              → {n : ℕ}
              → Δ ⊢ A₁ ∨ A₂ AT n
              → Δ ++ [ A₁ at n ] ⊢ B AT n
              → Δ ++ [ A₂ at n ] ⊢ B AT n
              ---------------------
              → Δ ⊢ B AT n
