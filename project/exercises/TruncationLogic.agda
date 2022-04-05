module exercises.TruncationLogic where
  open import Axiom.Extensionality.Propositional using (Extensionality)

  postulate fun-ext : ∀ {a b} → Extensionality a b

  open import Level
  open import Relation.Binary.PropositionalEquality using (_≡_; refl)
  import Data.Product
  import Data.Sum
  import Data.Empty
  import Data.Unit

  module 06-propositions-as-types where

  is-proposition : {ℓ : Level} → Set ℓ → Set ℓ
  is-proposition A = (x y : A) → x ≡ y

  record truncation-structure : Setω where
    field
      ∥_∥ : {ℓ : Level} → Set ℓ → Set (suc ℓ)
      ∥∥-is-proposition : {ℓ : Level} (A : Set ℓ) → is-proposition ∥ A ∥
      ∣_∣ : {ℓ : Level} {A : Set ℓ} → A → ∥ A ∥
      ∥∥-elim : {ℓ k : Level} {A : Set ℓ} {B : Set k} →
                is-proposition B → (A → B) → ∥ A ∥ → B

    infix 0 ∥_∥

    ∥∥-compute : {ℓ k : Level} {A : Set ℓ} {B : Set k} →
                 (i : (x y : B) → x ≡ y) (p : A → B) (a : A) → ∥∥-elim i p ∣ a ∣ ≡ p a
    ∥∥-compute i p a = i (∥∥-elim i p ∣ a ∣) (p a)


  module _ {ts : truncation-structure} where
    open Data.Product hiding (∃)
    open Data.Sum
    open Data.Empty
    open Data.Unit

    open truncation-structure ts public

    record HProp (ℓ : Level) : Set (suc ℓ) where
      constructor ⟨_,_⟩
      field
        proof : Set ℓ
        is-prop : is-proposition proof


    module _ {k ℓ : Level} where
      open HProp

      infixr 6 _∧ʰ_
      infixr 5 _∨ʰ_
      infixr 4 _⇒ʰ_

      ⊥ʰ : HProp zero
      ⊥ʰ = ⟨ ⊥ , (λ x y → ⊥-elim x) ⟩

      ⊤ʰ : HProp zero
      ⊤ʰ = ⟨ ⊤ , (λ _ _ → refl) ⟩

      _∧ʰ_ : HProp k → HProp ℓ → HProp (k ⊔ ℓ)
      ⟨ p , ξ ⟩ ∧ʰ ⟨ q , ζ ⟩ = ⟨ p × q , θ ⟩
        where
          θ : (x y : p × q) → x ≡ y
          θ (x₁ , y₁) (x₂ , y₂) with ξ x₁ x₂ | ζ y₁ y₂
          ... | refl | refl = refl

      _⇒ʰ_ : HProp k → HProp ℓ → HProp (k ⊔ ℓ)
      ⟨ p , ξ ⟩ ⇒ʰ ⟨ q , ζ ⟩ = ⟨ (p → q) , θ ⟩
        where
          θ : is-proposition (p → q)
          θ f g = fun-ext λ x → ζ(f x) (g x)

      _∨ʰ_ : HProp k → HProp ℓ → HProp (suc k ⊔ suc ℓ)
      ⟨ p , ξ ⟩ ∨ʰ ⟨ q , ζ ⟩ = ⟨ ∥ p ⊎ q ∥ , θ ⟩
        where
          θ : is-proposition ∥ p ⊎ q ∥
          θ = ∥∥-is-proposition _

      ∃ʰ : (A : Set k) → (A → HProp ℓ) → HProp (suc k ⊔ suc ℓ)
      ∃ʰ A ϕ = ⟨ ∥ Σ[ x ∈ A ] proof (ϕ x) ∥ , ∥∥-is-proposition _ ⟩

      ∀ʰ : (A : Set k) → (A → HProp ℓ) → HProp (k ⊔ ℓ)
      ∀ʰ A ϕ = ⟨ (∀ x → proof (ϕ x)) , (λ f g → fun-ext (λ x → is-prop (ϕ x) (f x) (g x))) ⟩

      -- We need to validate the rules of logic, here is a sample

      ∨ʰ-intro₁ : {A : HProp k} {B : HProp ℓ} → proof A → proof (A ∨ʰ B)
      ∨ʰ-intro₁ p = ∣ inj₁ p ∣

      ∃ʰ-elim : {m : Level} {A : Set k} (ϕ : A → HProp ℓ) (ψ : HProp m) →
               ((x : A) → proof (ϕ x) → proof ψ) → proof (∃ʰ A ϕ) → proof ψ
      ∃ʰ-elim ϕ ψ f p = ∥∥-elim (is-prop ψ) (λ { (x , q) → f x q }) p
