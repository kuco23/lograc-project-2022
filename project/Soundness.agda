open import HProp

module Soundness (AtomicFormula : Set) (η : AtomicFormula → HProp) where

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

l++[]≡l : {A : Set} (L : List A) → L ++ [] ≡ L 
l++[]≡l [] = refl
l++[]≡l (x ∷ L) = begin
    (x ∷ L) ++ []
  ≡⟨ cong (_++ []) refl ⟩
    (x ∷ []) ++ L ++ [] 
  ≡⟨ ++-assoc (x ∷ []) L [] ⟩
    (x ∷ []) ++ (L ++ []) 
  ≡⟨ cong ((x ∷ []) ++_) (l++[]≡l L) ⟩
    (x ∷ []) ++ L
  ∎

a∈≡ : {A : Set} {a : A} {L₁ L₂ : List A} → L₁ ≡ L₂ → a ∈ L₁ → a ∈ L₂
a∈≡ refl q = q

a∈l++a++d : {A : Set} (a : A) (L₁ L₂ : List A) → a ∈ L₁ ++ (a ∷ []) ++ L₂
a∈l++a++d a [] L₂ = ∈-here
a∈l++a++d a (x ∷ L₁) L₂ = a∈≡ aux₁ aux₃ where
  aux₁ : x ∷ (L₁ ++ (a ∷ []) ++ L₂) ≡ x ∷ L₁ ++ (a ∷ []) ++ L₂
  aux₁ = ++-assoc (x ∷ []) L₁ ((a ∷ []) ++ L₂)
  aux₃ : a ∈ x ∷ (L₁ ++ (a ∷ []) ++ L₂) 
  aux₃ = ∈-there {{a∈l++a++d a L₁ L₂}}

⟦_⟧ʰ : (Δ : Hypotheses) → HProp
⟦ [] ⟧ʰ = ⊤ʰ
⟦ δ at n ∷ Δ ⟧ʰ = ⟦ δ ⟧ n ∧ʰ ⟦ Δ ⟧ʰ

⟦x⟧→⟦[x]⟧ʰ : {n : ℕ} ((δ at n) : TimeFormula) → proof(⟦ δ ⟧ n) → proof(⟦ (δ at n) ∷ [] ⟧ʰ)
⟦x⟧→⟦[x]⟧ʰ (δ at n) = λ z → z , true

≡to→ : {Δ₁ Δ₂ : Hypotheses} → Δ₁ ≡ Δ₂ → proof(⟦ Δ₁ ⟧ʰ) → proof(⟦ Δ₂ ⟧ʰ)
≡to→ refl = λ z → z

split : (Δ₁ Δ₂ : Hypotheses) → proof(⟦ Δ₁ ++ Δ₂ ⟧ʰ) → proof(⟦ Δ₁ ⟧ʰ ∧ʰ ⟦ Δ₂ ⟧ʰ)
split [] Δ₂ p = true , p
split (x ∷ Δ₁) Δ₂ (p , q) with split Δ₁ Δ₂ q
... | q₁ , q₂ = (p , q₁) , q₂

join : (Δ₁ Δ₂ : Hypotheses) → proof(⟦ Δ₁ ⟧ʰ ∧ʰ ⟦ Δ₂ ⟧ʰ) → proof(⟦ Δ₁ ++ Δ₂ ⟧ʰ)
join [] Δ₂ (_ , q) = q
join (x ∷ Δ₁) Δ₂ ((p , q) , r) = p , join Δ₁ Δ₂ (q , r)

extract : {n : ℕ} {(δ at n) : TimeFormula} {Δ : Hypotheses} → (δ at n) ∈ Δ → proof(⟦ Δ ⟧ʰ) → proof(⟦ δ ⟧ n)
extract ∈-here (p , _) = p
extract {n} (∈-there {{x}}) (_ , q) = extract {n} x q

remove : (δ : TimeFormula) (Δ : Hypotheses) → proof(⟦ Δ ++ (δ ∷ []) ⟧ʰ) → proof(⟦ Δ ⟧ʰ)
remove δ Δ p = proj₁ (split Δ (δ ∷ []) p)

add : (δ : TimeFormula) (Δ : Hypotheses) → δ ∈ Δ → proof(⟦ Δ ⟧ʰ) → proof(⟦ Δ ++ (δ ∷ []) ⟧ʰ)
add (δ at n) Δ p q = aux₃ (aux₂ (aux₁ q)) where 
  aux₁ : proof(⟦ Δ ⟧ʰ) → proof(⟦ Δ ⟧ʰ ∧ʰ ⟦ δ ⟧ n)
  aux₁ q = q , (extract {n} {δ at n} {Δ} p q)
  aux₂ : proof(⟦ Δ ⟧ʰ ∧ʰ ⟦ δ ⟧ n) → proof(⟦ Δ ⟧ʰ ∧ʰ ⟦ δ at n ∷ [] ⟧ʰ)
  aux₂ (q₁ , q₂) = q₁ , ⟦x⟧→⟦[x]⟧ʰ{n} (δ at n) q₂
  aux₃ : proof(⟦ Δ ⟧ʰ ∧ʰ ⟦ δ at n ∷ [] ⟧ʰ) → proof(⟦ Δ ++ (δ at n) ∷ [] ⟧ʰ)
  aux₃ q = join Δ (δ at n ∷ []) q

shuffle : (Δ₁ Δ₂ Δ₃ : Hypotheses) → proof(⟦ Δ₁ ++ Δ₂ ++ Δ₃ ⟧ʰ) → proof(⟦ Δ₁ ++ Δ₃ ++ Δ₂ ⟧ʰ)
shuffle Δ₁ Δ₂ [] = ≡to→ aux where
  aux : Δ₁ ++ Δ₂ ++ [] ≡ Δ₁ ++ Δ₂
  aux = cong (Δ₁ ++_) (l++[]≡l Δ₂)
shuffle Δ₁ Δ₂ (x ∷ []) z = aux₅ (aux₄ (aux₃ (aux₂ (aux₁ z)))) where
  aux₁ : proof(⟦ Δ₁ ++ Δ₂ ++ (x ∷ []) ⟧ʰ) → proof(⟦ Δ₁ ⟧ʰ ∧ʰ ⟦ Δ₂ ++ (x ∷ []) ⟧ʰ)
  aux₁ = split Δ₁ (Δ₂ ++ (x ∷ []))
  aux₂ : proof(⟦ Δ₁ ⟧ʰ ∧ʰ ⟦ Δ₂ ++ (x ∷ []) ⟧ʰ) → proof(⟦ Δ₁ ⟧ʰ ∧ʰ (⟦ Δ₂ ⟧ʰ ∧ʰ ⟦ (x ∷ []) ⟧ʰ))
  aux₂ (p , q) = p , split Δ₂ (x ∷ []) q
  aux₃ : proof(⟦ Δ₁ ⟧ʰ ∧ʰ (⟦ Δ₂ ⟧ʰ ∧ʰ ⟦ (x ∷ []) ⟧ʰ)) → proof(⟦ Δ₁ ⟧ʰ ∧ʰ (⟦ (x ∷ []) ⟧ʰ ∧ʰ ⟦ Δ₂ ⟧ʰ))
  aux₃ (p , (q , r)) = p , (r , q)
  aux₄ : proof(⟦ Δ₁ ⟧ʰ ∧ʰ (⟦ (x ∷ []) ⟧ʰ ∧ʰ ⟦ Δ₂ ⟧ʰ)) → proof(⟦ Δ₁ ⟧ʰ ∧ʰ ⟦ (x ∷ []) ++ Δ₂ ⟧ʰ)
  aux₄ (p , (q , r))= p , join (x ∷ []) Δ₂ (q , r)
  aux₅ : proof(⟦ Δ₁ ⟧ʰ ∧ʰ ⟦ (x ∷ []) ++ Δ₂ ⟧ʰ) → proof(⟦ Δ₁ ++ ((x ∷ []) ++ Δ₂) ⟧ʰ)
  aux₅ p = join Δ₁ ((x ∷ []) ++ Δ₂) p
shuffle Δ₁ Δ₂ (x ∷ Δ₃) z = (≡to→ aux₅) (aux₄ ((≡to→ aux₃) (aux₂ ((≡to→ aux₁) z)))) where
  aux₁ : Δ₁ ++ Δ₂ ++ (x ∷ Δ₃) ≡ Δ₁ ++ (Δ₂ ++ (x ∷ [])) ++ Δ₃ 
  aux₁ = sym (cong (Δ₁ ++_) (++-assoc Δ₂ (x ∷ []) Δ₃))
  aux₂ : proof(⟦ Δ₁ ++ (Δ₂ ++ (x ∷ [])) ++ Δ₃ ⟧ʰ) → proof(⟦ Δ₁ ++ Δ₃ ++ (Δ₂ ++ (x ∷ [])) ⟧ʰ)
  aux₂ = shuffle Δ₁ (Δ₂ ++ (x ∷ [])) Δ₃
  aux₃ : Δ₁ ++ Δ₃ ++ (Δ₂ ++ (x ∷ [])) ≡ Δ₁ ++ (Δ₃ ++ Δ₂) ++ (x ∷ [])
  aux₃ = cong (Δ₁ ++_) (sym (++-assoc Δ₃ Δ₂ (x ∷ [])))
  aux₄ : proof(⟦ Δ₁ ++ (Δ₃ ++ Δ₂) ++ (x ∷ []) ⟧ʰ) → proof(⟦ Δ₁ ++ (x ∷ []) ++ (Δ₃ ++ Δ₂) ⟧ʰ)
  aux₄ = shuffle Δ₁ (Δ₃ ++ Δ₂) (x ∷ [])
  aux₅ : Δ₁ ++ (x ∷ []) ++ (Δ₃ ++ Δ₂) ≡ Δ₁ ++ (x ∷ Δ₃) ++ Δ₂
  aux₅ = sym (cong (Δ₁ ++_) refl)

Soundness : {Δ : Hypotheses} {δ : Formula} {n : ℕ} → Δ ⊢ δ AT n → proof(⟦ Δ ⟧ʰ) → proof(⟦ δ ⟧ n)

Soundness (weaken {Δ₁} {Δ₂} φ {ψ} {n} x) p = Soundness x (aux₃((≡to→ aux₂) (aux₁ p))) where
  aux₁ : proof(⟦ Δ₁ ++ (φ at n ∷ []) ++ Δ₂ ⟧ʰ) → proof(⟦ Δ₁ ++ Δ₂ ++ (φ at n ∷ []) ⟧ʰ)
  aux₁ p = shuffle Δ₁ (φ at n ∷ []) Δ₂ p
  aux₂ : Δ₁ ++ Δ₂ ++ (φ at n ∷ []) ≡ (Δ₁ ++ Δ₂) ++ (φ at n ∷ [])
  aux₂ = sym (++-assoc Δ₁ Δ₂ (φ at n ∷ []))
  aux₃ : proof(⟦ (Δ₁ ++ Δ₂) ++ (φ at n ∷ []) ⟧ʰ) → proof(⟦ Δ₁ ++ Δ₂ ⟧ʰ)
  aux₃ p = proj₁ (split (Δ₁ ++ Δ₂) (φ at n ∷ []) p)

Soundness (contract {Δ₁} {Δ₂} φ {ψ} {n} x) p = Soundness x (aux₅((≡to→ aux₄)((≡to→ aux₃) (aux₂ p)))) where
  aux₁ : proof(⟦ Δ₁ ++ φ at n ∷ [] ++ Δ₂ ⟧ʰ) → proof(⟦ (φ at n) ∷ [] ⟧ʰ)
  aux₁ p = ⟦x⟧→⟦[x]⟧ʰ {n} (φ at n) (extract {n} (a∈l++a++d (φ at n) Δ₁ Δ₂) p)
  aux₂ : proof(⟦ Δ₁ ++ φ at n ∷ [] ++ Δ₂ ⟧ʰ) → proof(⟦ (Δ₁ ++ φ at n ∷ [] ++ Δ₂) ++ φ at n ∷ [] ⟧ʰ)
  aux₂ p = join (Δ₁ ++ φ at n ∷ [] ++ Δ₂) (φ at n ∷ []) (p , aux₁ p)
  aux₃ : (Δ₁ ++ φ at n ∷ [] ++ Δ₂) ++ (φ at n ∷ []) ≡ Δ₁ ++ φ at n ∷ [] ++ Δ₂ ++ φ at n ∷ []
  aux₃ = ++-assoc Δ₁ (φ at n ∷ [] ++ Δ₂) (φ at n ∷ [])
  aux₄ : Δ₁ ++ φ at n ∷ [] ++ Δ₂ ++ φ at n ∷ [] ≡ Δ₁ ++ (φ at n ∷ [] ++ Δ₂) ++ φ at n ∷ []
  aux₄ = cong (Δ₁ ++_) (++-assoc (φ at n ∷ []) Δ₂ (φ at n ∷ []))
  aux₅ : proof(⟦ Δ₁ ++ (φ at n ∷ [] ++ Δ₂) ++ φ at n ∷ [] ⟧ʰ) → proof(⟦ Δ₁ ++ φ at n ∷ [] ++ φ at n ∷ [] ++ Δ₂ ⟧ʰ)
  aux₅ p = shuffle Δ₁ (φ at n ∷ [] ++ Δ₂) (φ at n ∷ []) p

Soundness (exchange {Δ₁} {Δ₂} φ₁ φ₂ {ψ} {n} x) p = {!!} where 
  aux₁ : Δ₁ ++ φ₂ at n ∷ φ₁ at n ∷ Δ₂ ≡ (Δ₁ ++ φ₂ at n ∷ [] ++ φ₁ at n ∷ []) ++ Δ₂
  aux₁ = {!   !}

Soundness (hyp _ _) p = {!!}

Soundness (⊥-elim x) p = {!!}

Soundness (⇒-intro x) p = λ x₁ → {!!}

Soundness (⇒-elim x x₂) p = {!!}

Soundness (X-intro x) p = Soundness x p

Soundness (X-elim x) p = Soundness x p

Soundness (G-intro x) p = λ x₁ x₂ → Soundness (x x₁ x₂) p

Soundness (G-elim x x₂) p = {!!}
  
 
