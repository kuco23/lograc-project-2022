open import TruncationLogic

module ExtensionLTL (AtomicFormula : Set) (ts : truncation-structure) where

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

module Formula where

       open import Data.List  using (List; []; _∷_; [_]; _++_) public

       {-
          Formulae of propositional logic.
       -}

       data Formula : Set where
                `_  : AtomicFormula → Formula           -- atomic formula
                ⊤   : Formula                           -- truth (unicode \top)
                ⊥   : Formula                           -- falsehood (unicode \bot)
                _∧_ : Formula → Formula → Formula       -- conjunction (unicode \wedge)
                _∨_ : Formula → Formula → Formula       -- disjunction (unicode \vee)
                _⇒_ : Formula → Formula → Formula       -- implication (unicode \=>)
                G_ : Formula → Formula
                _U_ : Formula → Formula → Formula
                X_ : Formula → Formula
  --              _⊃_ : Formula → Formula → Formula -- Unnecessary??? Book says it functions like an implication

       infixr 6 _∧_
       infixr 5 _∨_
       infixr 4 _⇒_
       infixr 20 G_
       infixr 20 _U_
       infixr 20 X_

module Semantics where -- TODO: Separate files for these different modules!

       open import Data.Bool renaming (_∧_ to _and_; _∨_ to _or_)
       open import TruncationLogic
       open import Level

       open import Data.Unit renaming (⊤ to One)
       -- TODO: Import empty type, product type, sum type, renaming as needed
       open Formula
       
       open truncation-structure ts public

       HProp0 = HProp {ts} zero 
       ℙ = HProp0
       Env = AtomicFormula → ℙ
       open import Data.Bool.Properties
       open import Data.Product

       {- Tu bi se naj to naredilo kot v semantics.agda iz Ex5
       Jaz, tega ne znam. Bom se moral vrniti sem. Ali pa
       ti narediš! -}
       ⟦_⟧ : Formula → Env → ℙ
       ⟦ ` P ⟧ η = η P
       ⟦ ⊤ ⟧ η = ⟨ One , (λ x y → {!!}) ⟩
       ⟦ ⊥ ⟧ η = ⟨ {!!} , {!!} ⟩
       ⟦ P ∧ Q ⟧ η = {!!!!}
       ⟦ P ∨ Q ⟧ η = {!!}
       ⟦ P ⇒ Q ⟧ η = {!!}
       ⟦ G P ⟧ η = {!!}
       ⟦ P U Q ⟧ η = {!!}
       ⟦ X P ⟧ η = {!!}

       {- Po tem, bi bil naslednji korak
       3. Validate some Axioms/Tautologies -}
