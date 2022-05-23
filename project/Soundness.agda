open import HProp

module Soundness (AtomicFormula : Set) (η : AtomicFormula → HProp) where

open import Agda.Builtin.Unit renaming (tt to true) hiding (⊤)

open import Data.Nat using (ℕ ; suc ; _≤_)
open import Data.Product using (_,_ ; proj₁ ; proj₂)
open import Data.Sum
open import Data.List
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

postulate lem : {(φ at n): TimeFormula} → proof(⟦ ¬ (¬ φ) ⟧ n) → proof(⟦ φ ⟧ n)

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

l≡k∧a∈l⇒a∈k : {A : Set} {a : A} {L₁ L₂ : List A} → L₁ ≡ L₂ → a ∈ L₁ → a ∈ L₂
l≡k∧a∈l⇒a∈k refl q = q

a∈l++[a]++d : {A : Set} (a : A) (L₁ L₂ : List A) → a ∈ L₁ ++ (a ∷ []) ++ L₂
a∈l++[a]++d a [] L₂ = ∈-here
a∈l++[a]++d a (x ∷ L₁) L₂ = l≡k∧a∈l⇒a∈k aux₁ aux₂ where
  aux₁ : x ∷ (L₁ ++ (a ∷ []) ++ L₂) ≡ x ∷ L₁ ++ (a ∷ []) ++ L₂
  aux₁ = ++-assoc (x ∷ []) L₁ ((a ∷ []) ++ L₂)
  aux₂ : a ∈ x ∷ (L₁ ++ (a ∷ []) ++ L₂) 
  aux₂ = ∈-there {{a∈l++[a]++d a L₁ L₂}}

⟦_⟧ʰ : (Δ : Hypotheses) → HProp
⟦ [] ⟧ʰ = ⊤ʰ
⟦ δ at n ∷ Δ ⟧ʰ = ⟦ δ ⟧ n ∧ʰ ⟦ Δ ⟧ʰ

⟦x⟧→⟦[x]⟧ʰ : ((δ at n) : TimeFormula) → proof(⟦ δ ⟧ n) → proof(⟦ [ δ at n ] ⟧ʰ)
⟦x⟧→⟦[x]⟧ʰ (δ at n) = λ z → z , true

⟦[x]⟧ʰ→⟦x⟧ : ((δ at n) : TimeFormula) → proof(⟦ [ δ at n ] ⟧ʰ) → proof(⟦ δ ⟧ n) 
⟦[x]⟧ʰ→⟦x⟧ (δ at n) = proj₁

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

add : (δ : TimeFormula) (Δ : Hypotheses) → δ ∈ Δ → proof(⟦ Δ ⟧ʰ) → proof(⟦ Δ ++ [ δ ] ⟧ʰ)
add (δ at n) Δ δ∈Δ p = aux₂ (aux₁ p) where 
  aux₁ : proof(⟦ Δ ⟧ʰ) → proof(⟦ Δ ⟧ʰ ∧ʰ ⟦ δ ⟧ n)
  aux₁ p = p , (extract {n} {δ at n} {Δ} δ∈Δ p)
  aux₂ : proof(⟦ Δ ⟧ʰ ∧ʰ ⟦ δ ⟧ n) → proof(⟦ Δ ++ [ δ at n ] ⟧ʰ)
  aux₂ (p₁ , p₂) = join Δ [ δ at n ] (p₁ , ⟦x⟧→⟦[x]⟧ʰ (δ at n) p₂)

shuffle : (Δ₁ Δ₂ Δ₃ : Hypotheses) → proof(⟦ Δ₁ ++ Δ₂ ++ Δ₃ ⟧ʰ) → proof(⟦ Δ₁ ++ Δ₃ ++ Δ₂ ⟧ʰ)
shuffle Δ₁ Δ₂ Δ₃ p with split Δ₁ (Δ₂ ++ Δ₃) p 
... | p₁ , q₁ with split Δ₂ Δ₃ q₁
... | p₂ , p₃ with join Δ₃ Δ₂ (p₃ , p₂)
... | x = join Δ₁ (Δ₃ ++ Δ₂) (p₁ , x)

shuffle₂ : (Δ₁ Δ₂ Δ₃ Δ₄ : Hypotheses) → proof(⟦ Δ₁ ++ Δ₂ ++ Δ₃ ++ Δ₄ ⟧ʰ) → proof(⟦ Δ₁ ++ Δ₃ ++ Δ₂ ++ Δ₄ ⟧ʰ)
shuffle₂ Δ₁ Δ₂ Δ₃ Δ₄ p with split Δ₁ (Δ₂ ++ Δ₃ ++ Δ₄) p
... | p₁ , q₁ with split Δ₂ (Δ₃ ++ Δ₄) q₁
... | p₂ , q₂ with split Δ₃ Δ₄ q₂ 
... | p₃ , p₄ with join Δ₂ Δ₄ (p₂ , p₄)
... | x₁ with join Δ₃ (Δ₂ ++ Δ₄) (p₃ , x₁)
... | x₂ = join Δ₁ (Δ₃ ++ Δ₂ ++ Δ₄) (p₁ , x₂)

Soundness : {Δ : Hypotheses} {δ : Formula} {n : ℕ} → Δ ⊢ δ AT n → proof(⟦ Δ ⟧ʰ) → proof(⟦ δ ⟧ n)

Soundness (weaken {Δ₁} {Δ₂} φ {ψ} {n} x) p = Soundness x (aux₃((≡to→ aux₂) (aux₁ p))) where
  aux₁ : proof(⟦ Δ₁ ++ [ φ at n ] ++ Δ₂ ⟧ʰ) → proof(⟦ Δ₁ ++ Δ₂ ++ [ φ at n ] ⟧ʰ)
  aux₁ p = shuffle Δ₁ ([ φ at n ]) Δ₂ p
  aux₂ : Δ₁ ++ Δ₂ ++ [ φ at n ] ≡ (Δ₁ ++ Δ₂) ++ [ φ at n ]
  aux₂ = sym (++-assoc Δ₁ Δ₂ ([ φ at n ]))
  aux₃ : proof(⟦ (Δ₁ ++ Δ₂) ++ [ φ at n ] ⟧ʰ) → proof(⟦ Δ₁ ++ Δ₂ ⟧ʰ)
  aux₃ p = proj₁ (split (Δ₁ ++ Δ₂) [ φ at n ] p)

Soundness (contract {Δ₁} {Δ₂} φ {ψ} {n} x) p = Soundness x (aux₃((≡to→ aux₂)(aux₁ p))) where
  aux₁ : proof(⟦ Δ₁ ++ [ φ at n ] ++ Δ₂ ⟧ʰ) → proof(⟦ (Δ₁ ++ [ φ at n ] ++ Δ₂) ++ [ φ at n ] ⟧ʰ)
  aux₁ p = add (φ at n) (Δ₁ ++ [ φ at n ] ++ Δ₂) (a∈l++[a]++d (φ at n) Δ₁ Δ₂) p
  aux₂ : (Δ₁ ++ [ φ at n ] ++ Δ₂) ++ [ φ at n ] ≡ Δ₁ ++ ([ φ at n ] ++ Δ₂) ++ [ φ at n ]
  aux₂ = begin 
      (Δ₁ ++ [ φ at n ] ++ Δ₂) ++ [ φ at n ]
    ≡⟨ ++-assoc Δ₁ ([ φ at n ] ++ Δ₂) [ φ at n ] ⟩
      Δ₁ ++ [ φ at n ] ++ Δ₂ ++ [ φ at n ]
    ≡⟨ cong (Δ₁ ++_) (++-assoc [ φ at n ] Δ₂ [ φ at n ]) ⟩
      Δ₁ ++ ([ φ at n ] ++ Δ₂) ++ [ φ at n ]
    ∎
  aux₃ : proof(⟦ Δ₁ ++ ([ φ at n ] ++ Δ₂) ++ [ φ at n ] ⟧ʰ) → proof(⟦ Δ₁ ++ [ φ at n ] ++ [ φ at n ] ++ Δ₂ ⟧ʰ)
  aux₃ p = shuffle Δ₁ ([ φ at n ] ++ Δ₂) ([ φ at n ]) p

Soundness (exchange {Δ₁} {Δ₂} φ₁ φ₂ {ψ} {m} {n} x) p = Soundness x (shuffle₂ Δ₁ [ φ₂ at n ] [ φ₁ at m ] Δ₂ p)

Soundness (hyp {Δ} φ n {{φₙ∈Δ}}) = extract {n} {φ at n} {Δ} φₙ∈Δ

Soundness (⊥-elim {Δ} {A} {n} {m} x) p = lem {A at n} (aux p) where 
  aux : proof(⟦ Δ ⟧ʰ) → (proof(⟦ (¬ A) ⟧ n) → proof(⟦ ⊥ ⟧ m)) -- = proof(⟦ ¬ ¬ A ⟧ n)
  aux p q = Soundness x (join Δ [ (¬ A) at n ] (p , ⟦x⟧→⟦[x]⟧ʰ ((¬ A) at n) q))

Soundness (⇒-intro {Δ} {A} {B} {n} x) p = λ q → Soundness x (join Δ [ A at n ] (p , ⟦x⟧→⟦[x]⟧ʰ (A at n) q))

Soundness (⇒-elim x₁ x₂) p = (Soundness x₁ p) (Soundness x₂ p)

Soundness (X-intro x) p = Soundness x p

Soundness (X-elim x) p = Soundness x p

Soundness (G-intro x) p = λ x₁ x₂ → Soundness (x x₁ x₂) p

Soundness (G-elim {m = m} x n≤m) p = (Soundness x p) m n≤m

Soundness ⊤-intro p = true

Soundness (∧-intro x₁ x₂) p = Soundness x₁ p , Soundness x₂ p

Soundness (∧-elim₁ x) p = proj₁ (Soundness x p)
Soundness (∧-elim₂ x) p = proj₂ (Soundness x p)

Soundness (∨-intro₁ x) p with Soundness x p 
... | q = {! q  !}
Soundness (∨-intro₂ x) p = {!   !}
Soundness (∨-elim x x₁ x₂) p = {!   !}
  