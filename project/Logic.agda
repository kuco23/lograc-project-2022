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
  --              _⊃_ : Formula → Formula → Formula -- Unnecessary??? Book says it functions like an implication

       infixr 6 _∧_
       infixr 5 _∨_
       infixr 4 _⇒_
       infixr 20 G_
       infixr 20 _U_
       infixr 20 X_
