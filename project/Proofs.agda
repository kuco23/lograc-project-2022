open import HProp

module Proofs (AtomicFormula : Set) (η : AtomicFormula → HProp) where


open import Agda.Builtin.Unit renaming (tt to true) hiding (⊤)

open import Data.Nat using (ℕ ; suc ; _≤_)
open import Data.Product using (_,_ ; proj₁ ; proj₂)
open import Data.List

import Relation.Binary.PropositionalEquality as Eq
open Eq renaming ([_] to [|_|])
open Eq.≡-Reasoning

import Logic
import Semantics
import NaturalDeduction

open module L = Logic AtomicFormula
open module S = Semantics AtomicFormula η
open module ND = NaturalDeduction AtomicFormula

lemma1 : (A : Formula) →
         (n m : ℕ) →
         (n ≤ m) →
         [ (G A) at n ]  ⊢ A AT m

lemma1 A n m p = G-elim (hyp (G A) n {{∈-here}}) p

lemma2 : (A : Formula)
            → (n : ℕ)
            → [ X A at n ] ⊢ A AT (suc n)
lemma2 A n = X-elim (hyp (X A) n {{∈-here}})

{-lemma2 : (A B C : Formula) →
                (n : ℕ) →
                G A at n ∷ [ G B at n ] ⊢ C AT n →
                -----------------------------
                [ G (A ∧ B) at n ] ⊢ C AT n
lemma2 A B C n x = {!!}-}

Ax1 : (A B : Formula) → (n : ℕ) → [] ⊢ (G (A ⇒ B) ⇒ (G A ⇒ G B)) AT n
Ax1 A B n = ⇒-intro (⇒-intro (
  G-intro (λ m p → ⇒-elim {A = A} 
    (G-elim (hyp (G (A ⇒ B)) n {{∈-here}}) p)
    (G-elim (hyp (G A) n {{∈-there {{∈-here}}}}) p))
  ))

Ax3 : (A : Formula) → (n : ℕ) → [] ⊢ (X (¬ A) ⇔ ¬ (X A)) AT n
Ax3 A n = ∧-intro left right where
  left : [] ⊢ X (¬ A) ⇒ ¬ X A AT n
  left = ⇒-intro ( ⇒-intro (⊥-elim {m = suc n} (⇒-elim {A = A} 
      (X-elim (hyp (X (¬ A)) n {{∈-here}})) 
      (X-elim (hyp (X A) n {{∈-there {{∈-here}}}}))
    )))
  right : [] ⊢ ¬ X A ⇒ X (¬ A) AT n
  right = ⇒-intro (X-intro (⇒-intro (⊥-elim {m = n} (⇒-elim {A = (X A)} 
      (hyp (¬ X A) n {{∈-here}}) 
      (X-intro (hyp A (suc n) {{∈-there {{∈-here}}}}))
    ))))