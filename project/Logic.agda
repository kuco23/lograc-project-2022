module Logic (AtomicFormula : Set) where
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
--              _⊃_ : Formula → Formula → Formula -- Unnecessary due to it being the same as ⇒

       ¬_ : Formula → Formula              -- unicode \neg
       ¬ φ = φ ⇒ ⊥
       
       _⇔_ : Formula → Formula → Formula    -- unicode \<=>
       φ ⇔ ψ = (φ ⇒ ψ) ∧ (ψ ⇒ φ)

       F_ : Formula → Formula
       F A = ¬ G (¬ A)   -- at some point in the future it will be true, for at least that one point

       infixr 6 _∧_
       infixr 5 _∨_
       infixr 4 _⇒_
       infixr 20 G_
       infixr 20 _U_
       infixr 20 X_
       infixr 20 F_

       infix 7 ¬_
       infix 3 _⇔_

      
