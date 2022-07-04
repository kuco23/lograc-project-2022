module auxListTheory where

open import Data.List using (List ; [] ; [_] ; _∷_ ; _++_)
open import Data.List.Properties using (++-assoc)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_ ; refl ; cong)
open Eq.≡-Reasoning

infix 3 _∈_
data _∈_ {A : Set} : A → List A → Set where
  instance
    ∈-here  : {x : A} → {xs : List A} → x ∈ (x ∷ xs)
    ∈-there : {x y : A} {xs : List A} → {{x ∈ xs}} → x ∈ (y ∷ xs)

l++[]≡l : {A : Set} (l : List A) → l ++ [] ≡ l 
l++[]≡l [] = refl
l++[]≡l (x ∷ l) = begin
    (x ∷ l) ++ []
  ≡⟨ cong (_++ []) refl ⟩
    [ x ] ++ l ++ [] 
  ≡⟨ ++-assoc [ x ] l [] ⟩
    [ x ] ++ (l ++ []) 
  ≡⟨ cong ([ x ] ++_) (l++[]≡l l) ⟩
    [ x ] ++ l
  ∎

a∈l₁++[a]++l₂ : {A : Set} (a : A) (l₁ l₂ : List A) → a ∈ l₁ ++ [ a ] ++ l₂
a∈l₁++[a]++l₂ a [] l₂ = ∈-here
a∈l₁++[a]++l₂ a (x ∷ l₁) l₂ = ∈-there {{a∈l₁++[a]++l₂ a l₁ l₂}}

a∈l₁⇒a∈l₁++l₂ : {A : Set} {a : A} {l₁ l₂ : List A} → a ∈ l₁ → a ∈ l₁ ++ l₂ 
a∈l₁⇒a∈l₁++l₂ ∈-here = ∈-here
a∈l₁⇒a∈l₁++l₂ {a = a} {l₁ = x ∷ l₁} {l₂ = l₂} (∈-there {{p}}) = ∈-there {{a∈l₁⇒a∈l₁++l₂ {l₁ = l₁} {l₂ = l₂} p}}

a∈l₂⇒a∈l₁++l₂ : {A : Set} {a : A} {l₁ l₂ : List A} → a ∈ l₂ → a ∈ l₁ ++ l₂ 
a∈l₂⇒a∈l₁++l₂ {l₁ = []} p = p
a∈l₂⇒a∈l₁++l₂ {l₁ = x ∷ l₁} {l₂ = l₂} p = ∈-there {{a∈l₂⇒a∈l₁++l₂ {l₁ = l₁} {l₂ = l₂} p}}