------------------------------------------------------------------------
-- Unary and binary relations
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Relation where

open import Equality.Propositional
open import Interval using (ext)
open import Prelude

open import Function-universe equality-with-J hiding (id; _∘_)

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
R ⁻¹ = R ∘ swap

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

-- Intersection of relations.

infixr 8 _∩_

_∩_ : ∀ {a ℓ₁ ℓ₂} {A : Set a} →
      Rel ℓ₁ A → Rel ℓ₂ A → Rel (ℓ₁ ⊔ ℓ₂) A
R ∩ S = λ x → R x × S x

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

-- Preservation lemmas for _⊆_.

infix 4 _⊆-cong_ _⊆-cong-→_

_⊆-cong_ :
  ∀ {k a r₁ r₂ s₁ s₂} {A : Set a}
    {R₁ : Rel r₁ A} {S₁ : Rel s₁ A}
    {R₂ : Rel r₂ A} {S₂ : Rel s₂ A} →
  (∀ {x} → R₁ x ↝[ ⌊ k ⌋-sym ] R₂ x) →
  (∀ {x} → S₁ x ↝[ ⌊ k ⌋-sym ] S₂ x) →
  R₁ ⊆ S₁ ↝[ ⌊ k ⌋-sym ] R₂ ⊆ S₂
R₁↝R₂ ⊆-cong S₁↝S₂ = implicit-∀-cong ext $ →-cong ext R₁↝R₂ S₁↝S₂

_⊆-cong-→_ :
  ∀ {a r₁ r₂ s₁ s₂} {A : Set a}
    {R₁ : Rel r₁ A} {S₁ : Rel s₁ A}
    {R₂ : Rel r₂ A} {S₂ : Rel s₂ A} →
  (∀ {x} → R₂ x → R₁ x) →
  (∀ {x} → S₁ x → S₂ x) →
  R₁ ⊆ S₁ → R₂ ⊆ S₂
R₂→R₁ ⊆-cong-→ S₁→S₂ = implicit-∀-cong ext $ →-cong-→ R₂→R₁ S₁→S₂

⊆-congʳ :
  ∀ {k a r s₁ s₂} {A : Set a}
    {R : Rel r A} {S₁ : Rel s₁ A} {S₂ : Rel s₂ A} →
  (∀ {x} → S₁ x ↝[ k ] S₂ x) →
  R ⊆ S₁ ↝[ k ] R ⊆ S₂
⊆-congʳ S₁↝S₂ = implicit-∀-cong ext $ ∀-cong ext λ _ → S₁↝S₂

-- Monotonicity of relation transformers.

Monotone :
  ∀ {a ℓ} {A : Set a} →
  Trans ℓ A → Set (a ⊔ lsuc ℓ)
Monotone F = ∀ {R S} → R ⊆ S → F R ⊆ F S

-- A definition that turns into a notion of symmetry if the first
-- argument is instantiated with the swap function. In that case this
-- definition is similar to one of those given by Pous and Sangiorgi
-- in Section 6.3.4.1 of "Enhancements of the bisimulation proof
-- method".

Symmetric : ∀ {ℓ} {I : Set ℓ} → (I → I) → Trans ℓ I → Set (lsuc ℓ)
Symmetric f F = ∀ R → F (R ∘ f) ⊆ F R ∘ f

-- If f is an involution, then the inclusion in Symmetric f F holds
-- also in the other direction.

involution→other-symmetry :
  ∀ {ℓ} {I : Set ℓ} (F : Trans ℓ I) {f : I → I} →
  f ∘ f ≡ id → Symmetric f F → ∀ R → F R ∘ f ⊆ F (R ∘ f)
involution→other-symmetry F {f} inv symm R =
  F R ∘ f            ⊆⟨ (λ {x} → subst (λ g → F (R ∘ g) (f x)) (sym inv)) ⟩
  F (R ∘ f ∘ f) ∘ f  ⊆⟨ symm _ ⟩
  F (R ∘ f) ∘ f ∘ f  ⊆⟨ (λ {x} → subst (λ g → F (R ∘ f) (g x)) inv) ⟩∎
  F (R ∘ f)          ∎
