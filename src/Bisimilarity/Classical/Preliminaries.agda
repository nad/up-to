------------------------------------------------------------------------
-- Some preliminaries
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Bisimilarity.Classical.Preliminaries where

open import Equality.Propositional
open import Prelude

-- Homogeneous binary relations.

Rel : ∀ {ℓ₁} ℓ₂ → Set ℓ₁ → Set (ℓ₁ ⊔ lsuc ℓ₂)
Rel ℓ A = A → A → Set ℓ

-- One kind of homogeneous binary relation transformers.

Trans : ∀ {a} ℓ → Set a → Set (a ⊔ lsuc ℓ)
Trans ℓ A = Rel ℓ A → Rel ℓ A

-- Composition of relations.

infixr 9 _⊙_

_⊙_ : ∀ {a ℓ₁ ℓ₂} {A : Set a} →
      Rel ℓ₁ A → Rel ℓ₂ A → Rel (a ⊔ ℓ₁ ⊔ ℓ₂) A
_R_ ⊙ _S_ = λ x z → ∃ λ y → (x R y) × (y S z)

-- Postcomposition with a function.

infixr 9 [_]⊙_

[_]⊙_ : ∀ {a ℓ₁ ℓ₂} {A : Set a} →
        (Set ℓ₁ → Set ℓ₂) → Rel ℓ₁ A → Rel ℓ₂ A
[ f ]⊙ _R_ = λ x y → f (x R y)

-- Composition of a relation with itself.

infix 10 _^^_

_^^_ : ∀ {a} {A : Set a} →
       Rel a A → ℕ → Rel a A
R ^^ zero  = _≡_
R ^^ suc n = R ⊙ R ^^ n

-- Union of relations.

infixr 7 _∪_

_∪_ : ∀ {a ℓ₁ ℓ₂} {A : Set a} →
      Rel ℓ₁ A → Rel ℓ₂ A → Rel (ℓ₁ ⊔ ℓ₂) A
_R_ ∪ _S_ = λ x y → x R y ⊎ x S y

-- Reflexive closure of relations.

_⁼ : ∀ {a ℓ} {A : Set a} →
     Rel ℓ A → Rel (a ⊔ ℓ) A
R ⁼ = R ∪ _≡_

-- Transitive closure of relations.

_⁺ : ∀ {a} {A : Set a} →
     Rel a A → Rel a A
R ⁺ = λ x y → ∃ λ n → (R ^^ (1 + n)) x y

-- Reflexive transitive closure of relations.

_* : ∀ {a} {A : Set a} →
     Rel a A → Rel a A
R * = λ x y → ∃ λ n → (R ^^ n) x y

-- The reflexive transitive closure is transitive.

*-trans : ∀ {a} {A : Set a} {_R_ : Rel a A} {x y z} →
          (_R_ *) x y → (_R_ *) y z → (_R_ *) x z
*-trans (zero  , refl)           aR*b = aR*b
*-trans (suc n , _ , aRb , bRⁿc) cR*d =
  Σ-map suc ((_ ,_) ∘ (aRb ,_))
    (*-trans (n , bRⁿc) cR*d)

-- Relation containment.

infix 4 _⊆_

_⊆_ : ∀ {a ℓ₁ ℓ₂} {A : Set a} →
      Rel ℓ₁ A → Rel ℓ₂ A → Set (a ⊔ ℓ₁ ⊔ ℓ₂)
_R_ ⊆ _S_ = ∀ x y → x R y → x S y

-- "Equational" reasoning combinators.

infix  -1 finally-⊆
infixr -2 _⊆⟨_⟩_ _⊆⟨⟩_

_⊆⟨_⟩_ : ∀ {a p q r} {A : Set a}
         (P : Rel p A) {Q : Rel q A} {R : Rel r A} →
         P ⊆ Q → Q ⊆ R → P ⊆ R
_ ⊆⟨ P⊆Q ⟩ Q⊆R = λ x y → Q⊆R x y ∘ P⊆Q x y

_⊆⟨⟩_ : ∀ {a p q} {A : Set a}
        (P : Rel p A) {Q : Rel q A} →
        P ⊆ Q → P ⊆ Q
_ ⊆⟨⟩ P⊆Q = P⊆Q

finally-⊆ : ∀ {a p q} {A : Set a}
            (P : Rel p A) (Q : Rel q A) →
            P ⊆ Q → P ⊆ Q
finally-⊆ _ _ P⊆Q = P⊆Q

syntax finally-⊆ P Q P⊆Q = P ⊆⟨ P⊆Q ⟩∎ Q ∎
