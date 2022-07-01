open import Data.Nat using (ℕ ; zero ; suc ; _≤_ ; z≤n ; s≤s)
open import HProp

module Soundness (AtomicFormula : Set) (η : AtomicFormula → ℕ → HProp) where

open import Agda.Builtin.Unit renaming (tt to true) hiding (⊤)
open import Data.List using (List ; [] ; [_] ; _∷_ ; _++_)
open import Data.List.Properties using (++-assoc)
open import Data.Product using (Σ ; _,_ ; proj₁ ; proj₂)
open import Data.Sum.Base

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_ ; refl ; cong ; sym)
open Eq.≡-Reasoning

open import Data.Nat.Properties using (_≤?_)
open import Relation.Nullary using (yes ; no)
open import AdvancedNumberTheory using (n≤n ; m≤n⇒m≤sn)
open import AdvancedListTheory using (_∈_ ; ∈-here ; ∈-there ; a∈l₁++[a]++l₂)

import Logic
import Semantics
import NaturalDeduction

open module L = Logic AtomicFormula
open module S = Semantics AtomicFormula η
open module ND = NaturalDeduction AtomicFormula


⊥⇒⋆ : {n : ℕ} {φ : Formula} → proof(⟦ ⊥ ⟧ n) → proof(⟦ φ ⟧ n)
⊥⇒⋆ ()

⟦_⟧ʰ : (Δ : Hypotheses) → HProp
⟦ [] ⟧ʰ = ⊤ʰ
⟦ δ at n ∷ Δ ⟧ʰ = ⟦ δ ⟧ n ∧ʰ ⟦ Δ ⟧ʰ

≡to→ : {Δ₁ Δ₂ : Hypotheses} → Δ₁ ≡ Δ₂ → proof(⟦ Δ₁ ⟧ʰ) → proof(⟦ Δ₂ ⟧ʰ)
≡to→ refl = λ z → z

⟦x⟧→⟦[x]⟧ʰ : ((δ at n) : TimeFormula) → proof(⟦ δ ⟧ n) → proof(⟦ [ δ at n ] ⟧ʰ)
⟦x⟧→⟦[x]⟧ʰ (δ at n) = λ z → z , true

split : (Δ₁ Δ₂ : Hypotheses) → proof(⟦ Δ₁ ++ Δ₂ ⟧ʰ) → proof(⟦ Δ₁ ⟧ʰ ∧ʰ ⟦ Δ₂ ⟧ʰ)
split [] Δ₂ p = true , p
split (x ∷ Δ₁) Δ₂ (p , q) with split Δ₁ Δ₂ q
... | q₁ , q₂ = (p , q₁) , q₂

join : (Δ₁ Δ₂ : Hypotheses) → proof(⟦ Δ₁ ⟧ʰ) → proof(⟦ Δ₂ ⟧ʰ) → proof(⟦ Δ₁ ++ Δ₂ ⟧ʰ)
join [] Δ₂ _ q = q
join (x ∷ Δ₁) Δ₂ (p , q) r = p , join Δ₁ Δ₂ q r

extract : {n : ℕ} {(δ at n) : TimeFormula} {Δ : Hypotheses} → (δ at n) ∈ Δ → proof(⟦ Δ ⟧ʰ) → proof(⟦ δ ⟧ n)
extract ∈-here (p , _) = p
extract {n} (∈-there {{x}}) (_ , q) = extract {n} x q

add : (δ : TimeFormula) (Δ : Hypotheses) → δ ∈ Δ → proof(⟦ Δ ⟧ʰ) → proof(⟦ Δ ++ [ δ ] ⟧ʰ)
add (δ at n) Δ δ∈Δ p = aux₂ (aux₁ p) where 
  aux₁ : proof(⟦ Δ ⟧ʰ) → proof(⟦ Δ ⟧ʰ ∧ʰ ⟦ δ ⟧ n)
  aux₁ p = p , (extract {n} {δ at n} {Δ} δ∈Δ p)
  aux₂ : proof(⟦ Δ ⟧ʰ ∧ʰ ⟦ δ ⟧ n) → proof(⟦ Δ ++ [ δ at n ] ⟧ʰ)
  aux₂ (p₁ , p₂) = join Δ [ δ at n ] p₁ (⟦x⟧→⟦[x]⟧ʰ (δ at n) p₂)

shuffle₃ : (Δ₁ Δ₂ Δ₃ : Hypotheses) → proof(⟦ Δ₁ ++ Δ₂ ++ Δ₃ ⟧ʰ) → proof(⟦ Δ₁ ++ Δ₃ ++ Δ₂ ⟧ʰ)
shuffle₃ Δ₁ Δ₂ Δ₃ p with split Δ₁ (Δ₂ ++ Δ₃) p 
... | p₁ , q₁ with split Δ₂ Δ₃ q₁
... | p₂ , p₃ with join Δ₃ Δ₂ p₃ p₂
... | x = join Δ₁ (Δ₃ ++ Δ₂) p₁ x

shuffle₄ : (Δ₁ Δ₂ Δ₃ Δ₄ : Hypotheses) → proof(⟦ Δ₁ ++ Δ₂ ++ Δ₃ ++ Δ₄ ⟧ʰ) → proof(⟦ Δ₁ ++ Δ₃ ++ Δ₂ ++ Δ₄ ⟧ʰ)
shuffle₄ Δ₁ Δ₂ Δ₃ Δ₄ p with split Δ₁ (Δ₂ ++ Δ₃ ++ Δ₄) p
... | p₁ , q₁ with split Δ₂ (Δ₃ ++ Δ₄) q₁
... | p₂ , q₂ with split Δ₃ Δ₄ q₂ 
... | p₃ , p₄ with join Δ₂ Δ₄ p₂ p₄
... | x₁ with join Δ₃ (Δ₂ ++ Δ₄) p₃ x₁
... | x₂ = join Δ₁ (Δ₃ ++ Δ₂ ++ Δ₄) p₁ x₂

Soundness : {Δ : Hypotheses} {δ : Formula} {n : ℕ} → Δ ⊢ δ AT n → proof(⟦ Δ ⟧ʰ) → proof(⟦ δ ⟧ n)

Soundness (weaken {Δ₁} {Δ₂} φ {n = n} x) p = Soundness x (aux₃((≡to→ aux₂) (aux₁ p))) where
  aux₁ : proof(⟦ Δ₁ ++ [ φ at n ] ++ Δ₂ ⟧ʰ) → proof(⟦ Δ₁ ++ Δ₂ ++ [ φ at n ] ⟧ʰ)
  aux₁ p = shuffle₃ Δ₁ ([ φ at n ]) Δ₂ p
  aux₂ : Δ₁ ++ Δ₂ ++ [ φ at n ] ≡ (Δ₁ ++ Δ₂) ++ [ φ at n ]
  aux₂ = sym (++-assoc Δ₁ Δ₂ ([ φ at n ]))
  aux₃ : proof(⟦ (Δ₁ ++ Δ₂) ++ [ φ at n ] ⟧ʰ) → proof(⟦ Δ₁ ++ Δ₂ ⟧ʰ)
  aux₃ p = proj₁ (split (Δ₁ ++ Δ₂) [ φ at n ] p)

Soundness (contract {Δ₁} {Δ₂} φ {n = n} x) p = Soundness x (aux₃((≡to→ aux₂)(aux₁ p))) where
  aux₁ : proof(⟦ Δ₁ ++ [ φ at n ] ++ Δ₂ ⟧ʰ) → proof(⟦ (Δ₁ ++ [ φ at n ] ++ Δ₂) ++ [ φ at n ] ⟧ʰ)
  aux₁ p = add (φ at n) (Δ₁ ++ [ φ at n ] ++ Δ₂) (a∈l₁++[a]++l₂ (φ at n) Δ₁ Δ₂) p
  aux₂ : (Δ₁ ++ [ φ at n ] ++ Δ₂) ++ [ φ at n ] ≡ Δ₁ ++ ([ φ at n ] ++ Δ₂) ++ [ φ at n ]
  aux₂ = begin 
      (Δ₁ ++ [ φ at n ] ++ Δ₂) ++ [ φ at n ]
    ≡⟨ ++-assoc Δ₁ ([ φ at n ] ++ Δ₂) [ φ at n ] ⟩
      Δ₁ ++ [ φ at n ] ++ Δ₂ ++ [ φ at n ]
    ≡⟨ cong (Δ₁ ++_) (++-assoc [ φ at n ] Δ₂ [ φ at n ]) ⟩
      Δ₁ ++ ([ φ at n ] ++ Δ₂) ++ [ φ at n ]
    ∎
  aux₃ : proof(⟦ Δ₁ ++ ([ φ at n ] ++ Δ₂) ++ [ φ at n ] ⟧ʰ) → proof(⟦ Δ₁ ++ [ φ at n ] ++ [ φ at n ] ++ Δ₂ ⟧ʰ)
  aux₃ p = shuffle₃ Δ₁ ([ φ at n ] ++ Δ₂) ([ φ at n ]) p

Soundness (exchange {Δ₁} {Δ₂} φ₁ φ₂ {m = m} {n = n} x) p = Soundness x (shuffle₄ Δ₁ [ φ₂ at n ] [ φ₁ at m ] Δ₂ p)

Soundness (hyp {Δ} φ n {{φₙ∈Δ}}) = extract {n} {φ at n} {Δ} φₙ∈Δ

Soundness (⊥-elim {φ = φ} {n = n} x) p = ⊥⇒⋆ {n} {φ} (Soundness x p)

Soundness ⊤-intro p = true

Soundness (∧-intro x₁ x₂) p = Soundness x₁ p , Soundness x₂ p

Soundness (∧-elim₁ x) p = proj₁ (Soundness x p)
Soundness (∧-elim₂ x) p = proj₂ (Soundness x p)

Soundness (∨-intro₁ x) p = ∣ inj₁ (Soundness x p) ∣
Soundness (∨-intro₂ x) p = ∣ inj₂ (Soundness x p) ∣

Soundness {Δ} {δ} (∨-elim {Δ} {φ₁} {φ₂} {n = n} x x₁ x₂) p = ∥∥-elim (is-prop (⟦ δ ⟧ n)) aux (Soundness x p) where
  aux : proof (⟦ φ₁ ⟧ n) ⊎ proof (⟦ φ₂ ⟧ n) → proof(⟦ δ ⟧ n)
  aux (inj₁ p₁) = Soundness x₁ (join Δ [ φ₁ at n ] p (⟦x⟧→⟦[x]⟧ʰ (φ₁ at n) p₁))
  aux (inj₂ p₂) = Soundness x₂ (join Δ [ φ₂ at n ] p (⟦x⟧→⟦[x]⟧ʰ (φ₂ at n) p₂))

Soundness (⇒-intro {Δ} {φ} {n = n} x) p = λ q → Soundness x (join Δ [ φ at n ] p (⟦x⟧→⟦[x]⟧ʰ (φ at n) q))

Soundness (⇒-elim x₁ x₂) p = (Soundness x₁ p) (Soundness x₂ p)

Soundness (X-intro x) p = Soundness x p

Soundness (X-elim x) p = Soundness x p

Soundness (G-intro x) p = λ x₁ x₂ → Soundness (x x₁ x₂) p

Soundness (G-elim {m = m} n≤m x) p = (Soundness x p) m n≤m

Soundness (U-intro {m = m} n≤m Δ⊢ψₘ Δ⊢φₖ) p = ∣ 
    m , n≤m , Soundness Δ⊢ψₘ p , 
    (λ x₁ x₂ → Soundness (Δ⊢φₖ x₁ (proj₁ x₂) (proj₂ x₂)) p)
  ∣

Soundness (U-elim {Δ} {φ} {ψ} {ρ} {n} {k} f Δ⊢φUψₙ) p = ∥∥-elim (is-prop(⟦ ρ ⟧ k)) aux₂ (Soundness Δ⊢φUψₙ p) where 
  aux₁ : {m n : ℕ} {φ : Formula} → n ≤ m 
      → ((x₄ : ℕ) → Σ (n ≤ x₄) (λ x₅ → suc x₄ ≤ m) → proof(⟦ φ ⟧ x₄))
      → proof ⟦ time-range φ n m ⟧ʰ
  aux₁ {zero} p f = true
  aux₁ {suc m} {n} {φ} p f with n ≤? m
  ... | yes n≤m = (f m) (n≤m , n≤n) , aux₁ {m} {n} n≤m aux₁₁ where
      aux₁₁ : (x₄ : ℕ) → Σ (n ≤ x₄) (λ x₅ → suc x₄ ≤ m) → proof(⟦ φ ⟧ x₄)
      aux₁₁ x₄ (n≤x₄ , sx₄≤m) = (f x₄) (n≤x₄ , (m≤n⇒m≤sn sx₄≤m))
  ... | no _ = true
  aux₂ : Σ ℕ (λ x₁ → Σ (n ≤ x₁) (λ x₂ → Σ (proof (⟦ ψ ⟧ x₁)) (λ x₃ → (x₄ : ℕ) → Σ (n ≤ x₄) (λ x₅ → suc x₄ ≤ x₁) → proof (⟦ φ ⟧ x₄)))) 
      → proof (⟦ ρ ⟧ k)
  aux₂ (m , n≤m , q , g) = Soundness (f m n≤m) aux₂₁ where 
    aux₂₁ : proof(⟦ Δ ++ time-range φ n m ++ [ ψ at m ] ⟧ʰ)
    aux₂₁ = join Δ (time-range φ n m ++ [ ψ at m ]) p (join (time-range φ n m) [ ψ at m ] (aux₁ n≤m g) (⟦x⟧→⟦[x]⟧ʰ (ψ at m) q))
