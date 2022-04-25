

{-
Prop logic φ,ψ ∷= P | ⊤ | ⊥ | φ ∧ ψ | φ ∨ ψ | φ ⇒ ψ 
Temporal logic LTL φ ∷= ... | Gφ | φ U ψ | Xφ
G-for all future times
X-for next future time
U-φ holds until ψ holds


1. Extend formula with modalities
2. define semantics of φ
3. validate some axioms/tautologies
4. do the other more involved stuff - DON'T WORRY ABOUT IT UNTIL WE GET PAST 3.

prop. logic :
  ⟦φ⟧ : Env → HProp
temporal logics:
  (W, R, V) a Kripke frame
    W - set of time (can be natural numbers)
    R - relation on W (say <)
    V - map from W → (AtomFormulae → HProp) (ie P(AtomicFormulae))
      for a given W it gives whether the AtomFormula is true
      For Temporal logic: ⟦φ⟧L : ℕ → HProp

⟦φ⟧(W,R,V) : W → HProp

w| ⊢ φ : HProp
⟦φ⟧ (w) : HProp
both of these the same

Location of HProp: http://www.andrej.com/zapiski/ISRM-LOGRAC-2022/06-propositions-as-types.lagda.html

Location of Logic: exercises a week before 25. 3. 2022

Recommendation: Generalize Natural numbers a bit

Change semantics.agda so that it maps to HProp instead of Bool

Use HoTT to get the semantics and ideas for how to do any of this

CURRENT PROJECT: MAKE IT WORK LIKE SEMANTICS.AGDA
-}


open import HProp


module Semantics (AtomicFormula : Set) (η : AtomicFormula → HProp) where -- TODO: Separate files for these different modules!

      open import Data.Nat using (ℕ ; suc)

      open import Data.Product hiding (∃)
      open import Data.Sum
      open import Data.Unit renaming (⊤ to One)
      open import Data.Empty renaming (⊥ to Zero)

      open import Data.Bool renaming (_∧_ to _and_; _∨_ to _or_)
      open import Data.Bool.Properties

      open import Relation.Binary.PropositionalEquality using (_≡_; refl)

      open import HProp
      open import Logic AtomicFormula
      open import Data.Nat --for ≥ 

      ℙ = HProp
      Env = AtomicFormula → ℙ

      ⟦_⟧ : Formula → ℕ  → ℙ
      ⟦ ` P ⟧ n = η P
      ⟦ ⊤ ⟧ n = ⊤ʰ
      ⟦ ⊥ ⟧ n = ⊥ʰ
      ⟦ P ∧ Q ⟧ n = ⟦ P ⟧ n ∧ʰ ⟦ Q ⟧ n
      ⟦ P ∨ Q ⟧ n = ⟦ P ⟧ n ∨ʰ ⟦ Q ⟧ n
      ⟦ P ⇒ Q ⟧ n = ⟦ P ⟧ n ⇒ʰ ⟦ Q ⟧ n
      ⟦ G P ⟧ n = ∀ʰ ℕ ((λ m → (n ≤ʰ m) ⇒ʰ ⟦ P ⟧ m))
      ⟦ P U Q ⟧ n = ∃ʰ ℕ  (λ n' → ((n ≤ʰ n') ∧ʰ ((⟦ Q ⟧) n' ∧ʰ (∀ʰ ℕ (λ m → (((n ≤ʰ m) ∧ʰ (m <ʰ n')) ⇒ʰ ⟦ P ⟧ m))))))
      ⟦ X P ⟧ n = ⟦ P ⟧ (suc n)
