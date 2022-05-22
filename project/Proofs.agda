open import HProp

module Proofs (AtomicFormula : Set) (η : AtomicFormula → HProp) where


open import Agda.Builtin.Unit renaming (tt to true) hiding (⊤)

open import Data.Nat using (ℕ ; suc ; _≤_)
open import Data.Product using (_,_ ; proj₁ ; proj₂)
open import Data.List.Properties

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
         [ G A at n ] ⊢ A AT m

lemma1 A n m p = G-elim {![ G A at n ] ⊢ G A AT n!} p

Ax1 : (A B : Formula) →
         (n : ℕ) →
         [] ⊢ (G (A ⇒ B) ⇒ (G A ⇒ G B)) AT n
Ax1 A B n = ⇒-intro (⇒-intro (G-intro {!!} ))

