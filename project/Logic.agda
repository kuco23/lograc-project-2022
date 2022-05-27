module Logic (AtomicFormula : Set) where

       -- open import Data.List  using (List; []; _∷_; [_]; _++_) public

       data Formula : Set where
                `_  : AtomicFormula → Formula           -- atomic formula
                ⊤   : Formula                           -- truth (unicode \top)
                ⊥   : Formula                           -- falsehood (unicode \bot)
                _∧_ : Formula → Formula → Formula       -- conjunction (unicode \wedge)
                _∨_ : Formula → Formula → Formula       -- disjunction (unicode \vee)
                _⇒_ : Formula → Formula → Formula       -- implication (unicode \=>)
                G_ : Formula → Formula                  -- G A n ⇔ A m for all m ≥ n 
                _U_ : Formula → Formula → Formula       -- A U B n ⇔ exists m ≥= n. A holds from n to (m - 1)
                X_ : Formula → Formula                  -- X A n ⇔ A (n + 1)

       ¬_ : Formula → Formula              -- unicode \neg
       ¬ φ = φ ⇒ ⊥
       
       _⇔_ : Formula → Formula → Formula    -- unicode \<=>
       φ ⇔ ψ = (φ ⇒ ψ) ∧ (ψ ⇒ φ)

       F_ : Formula → Formula
       F A = ¬ G (¬ A)   -- F A ⇔ A is true for at least one point in the future

       infixr 6 _∧_
       infixr 5 _∨_
       infixr 4 _⇒_
       infixr 20 G_
       infixr 20 _U_
       infixr 20 X_
       infixr 20 F_

       infix 7 ¬_
       infix 3 _⇔_