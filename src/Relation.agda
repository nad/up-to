------------------------------------------------------------------------
-- Unary and binary relations
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Relation where

open import Equality.Propositional
open import Prelude

-- Unary relations.

Rel : ∀ {ℓ₁} ℓ₂ → Set ℓ₁ → Set (ℓ₁ ⊔ lsuc ℓ₂)
Rel ℓ A = A → Set ℓ

-- Homogeneous binary relations.

Rel₂ : ∀ {ℓ₁} ℓ₂ → Set ℓ₁ → Set (ℓ₁ ⊔ lsuc ℓ₂)
Rel₂ ℓ A = Rel ℓ (A × A)

-- One kind of unary relation transformer.

Trans : ∀ {a} ℓ → Set a → Set (a ⊔ lsuc ℓ)
Trans ℓ A = Rel ℓ A → Rel ℓ A

-- One kind of binary relation transformer.

Trans₂ : ∀ {a} ℓ → Set a → Set (a ⊔ lsuc ℓ)
Trans₂ ℓ A = Trans ℓ (A × A)

-- The converse of a binary relation.

infixr 10 _⁻¹

_⁻¹ : ∀ {a ℓ} {A : Set a} → Rel₂ ℓ A → Rel₂ ℓ A
(R ⁻¹) (x , y) = R (y , x)

-- Composition of binary relations.

infixr 9 _⊙_

_⊙_ : ∀ {a ℓ₁ ℓ₂} {A : Set a} →
      Rel₂ ℓ₁ A → Rel₂ ℓ₂ A → Rel₂ (a ⊔ ℓ₁ ⊔ ℓ₂) A
(R ⊙ S) (x , z) = ∃ λ y → R (x , y) × S (y , z)

-- Composition of a binary relation with itself.

infix 10 _^^_

_^^_ : ∀ {a} {A : Set a} →
       Rel₂ a A → ℕ → Rel₂ a A
R ^^ zero  = uncurry _≡_
R ^^ suc n = R ⊙ R ^^ n

-- Union of relations.

infixr 7 _∪_

_∪_ : ∀ {a ℓ₁ ℓ₂} {A : Set a} →
      Rel ℓ₁ A → Rel ℓ₂ A → Rel (ℓ₁ ⊔ ℓ₂) A
R ∪ S = λ x → R x ⊎ S x

-- Reflexive closure of binary relations.

_⁼ : ∀ {a ℓ} {A : Set a} →
     Rel₂ ℓ A → Rel₂ (a ⊔ ℓ) A
R ⁼ = R ∪ uncurry _≡_

-- Transitive closure of binary relations.

_⁺ : ∀ {a} {A : Set a} →
     Rel₂ a A → Rel₂ a A
(R ⁺) x = ∃ λ n → (R ^^ (1 + n)) x

-- Reflexive transitive closure of binary relations.

_* : ∀ {a} {A : Set a} →
     Rel₂ a A → Rel₂ a A
(R *) x = ∃ λ n → (R ^^ n) x

-- The reflexive transitive closure is transitive.

*-trans : ∀ {a} {A : Set a} {R : Rel₂ a A} {x y z} →
          (R *) (x , y) → (R *) (y , z) → (R *) (x , z)
*-trans (zero  , refl)           aR*b = aR*b
*-trans (suc n , _ , aRb , bRⁿc) cR*d =
  Σ-map suc ((_ ,_) ∘ (aRb ,_))
    (*-trans (n , bRⁿc) cR*d)

-- Relation containment.

infix 4 _⊆_

_⊆_ : ∀ {a ℓ₁ ℓ₂} {A : Set a} →
      Rel ℓ₁ A → Rel ℓ₂ A → Set (a ⊔ ℓ₁ ⊔ ℓ₂)
R ⊆ S = ∀ {x} → R x → S x

-- Monotonicity of relation transformers.

Monotone :
  ∀ {a ℓ} {A : Set a} →
  Trans ℓ A → Set (a ⊔ lsuc ℓ)
Monotone F = ∀ {R S} → R ⊆ S → F R ⊆ F S

-- "Equational" reasoning combinators.

infix  -1 finally-⊆
infixr -2 _⊆⟨_⟩_ _⊆⟨⟩_

_⊆⟨_⟩_ : ∀ {a p q r} {A : Set a}
         (P : Rel p A) {Q : Rel q A} {R : Rel r A} →
         P ⊆ Q → Q ⊆ R → P ⊆ R
_ ⊆⟨ P⊆Q ⟩ Q⊆R = Q⊆R ∘ P⊆Q

_⊆⟨⟩_ : ∀ {a p q} {A : Set a}
        (P : Rel p A) {Q : Rel q A} →
        P ⊆ Q → P ⊆ Q
_ ⊆⟨⟩ P⊆Q = P⊆Q

finally-⊆ : ∀ {a p q} {A : Set a}
            (P : Rel p A) (Q : Rel q A) →
            P ⊆ Q → P ⊆ Q
finally-⊆ _ _ P⊆Q = P⊆Q

syntax finally-⊆ P Q P⊆Q = P ⊆⟨ P⊆Q ⟩∎ Q ∎
