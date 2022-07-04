module auxListTheory where

open import Data.List using (List ; [] ; [_] ; _∷_ ; _++_)

infix 3 _∈_
data _∈_ {A : Set} : A → List A → Set where
  instance
    ∈-here  : {x : A} → {xs : List A} → x ∈ (x ∷ xs)
    ∈-there : {x y : A} {xs : List A} → {{x ∈ xs}} → x ∈ (y ∷ xs)

a∈l₁++[a]++l₂ : {A : Set} (a : A) (l₁ l₂ : List A) → a ∈ l₁ ++ [ a ] ++ l₂
a∈l₁++[a]++l₂ a [] l₂ = ∈-here
a∈l₁++[a]++l₂ a (x ∷ l₁) l₂ = ∈-there {{a∈l₁++[a]++l₂ a l₁ l₂}}

a∈l₁⇒a∈l₁++l₂ : {A : Set} {a : A} {l₁ l₂ : List A} → a ∈ l₁ → a ∈ l₁ ++ l₂ 
a∈l₁⇒a∈l₁++l₂ ∈-here = ∈-here
a∈l₁⇒a∈l₁++l₂ {a = a} {l₁ = x ∷ l₁} {l₂ = l₂} (∈-there {{p}}) = ∈-there {{a∈l₁⇒a∈l₁++l₂ {l₁ = l₁} {l₂ = l₂} p}}

a∈l₂⇒a∈l₁++l₂ : {A : Set} {a : A} {l₁ l₂ : List A} → a ∈ l₂ → a ∈ l₁ ++ l₂ 
a∈l₂⇒a∈l₁++l₂ {l₁ = []} p = p
a∈l₂⇒a∈l₁++l₂ {l₁ = x ∷ l₁} {l₂ = l₂} p = ∈-there {{a∈l₂⇒a∈l₁++l₂ {l₁ = l₁} {l₂ = l₂} p}}