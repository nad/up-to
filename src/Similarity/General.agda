------------------------------------------------------------------------
-- A parametrised coinductive definition that can be used to define
-- various forms of similarity
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

open import Labelled-transition-system

module Similarity.General
         {ℓ}
         (lts : LTS ℓ)
         (open LTS lts)
         (_[_]↝_ : Proc → Label → Proc → Set ℓ)
         (⟶→↝ : ∀ {p μ q} → p [ μ ]⟶ q → p [ μ ]↝ q)
         where

open import Equality.Propositional as Eq hiding (Extensionality)
open import Prelude

open import Bijection equality-with-J using (_↔_)
open import Function-universe equality-with-J hiding (id; _∘_)

open import Indexed-container hiding (⟨_⟩)
open import Relation
open import Similarity.Step lts _[_]↝_ as Step public
  using (S̲t̲e̲p̲)

open Indexed-container public using (force)
open S̲t̲e̲p̲ public using (⟨_⟩; challenge)

-- Similarity. Note that this definition is small.

infix 4 _≤_ _≤′_ [_]_≤_ [_]_≤′_

Similarity : Size → Rel₂ ℓ Proc
Similarity i = ν S̲t̲e̲p̲ i

Similarity′ : Size → Rel₂ ℓ Proc
Similarity′ i = ν′ S̲t̲e̲p̲ i

[_]_≤_ : Size → Proc → Proc → Set ℓ
[_]_≤_ = curry ∘ Similarity

[_]_≤′_ : Size → Proc → Proc → Set ℓ
[_]_≤′_ = curry ∘ Similarity′

_≤_ : Proc → Proc → Set ℓ
_≤_ = [ ∞ ]_≤_

_≤′_ : Proc → Proc → Set ℓ
_≤′_ = [ ∞ ]_≤′_

-- Similarity is reflexive.

mutual

  reflexive-≤ : ∀ {p i} → [ i ] p ≤ p
  reflexive-≤ =
    S̲t̲e̲p̲.⟨ (λ p⟶p′ → _ , ⟶→↝ p⟶p′ , reflexive-≤′)
         ⟩

  reflexive-≤′ : ∀ {p i} → [ i ] p ≤′ p
  force reflexive-≤′ = reflexive-≤

≡⇒≤ : ∀ {p q} → p ≡ q → p ≤ q
≡⇒≤ refl = reflexive-≤

-- Functions that can be used to aid the instance resolution
-- mechanism.

infix -2 ≤:_ ≤′:_

≤:_ : ∀ {i p q} → [ i ] p ≤ q → [ i ] p ≤ q
≤:_ = id

≤′:_ : ∀ {i p q} → [ i ] p ≤′ q → [ i ] p ≤′ q
≤′:_ = id

-- Bisimilarity of similarity proofs.

infix 4 [_]_≡_ [_]_≡′_

[_]_≡_ : ∀ {p q} → Size → (_ _ : ν S̲t̲e̲p̲ ∞ (p , q)) → Set ℓ
[_]_≡_ = curry ∘ ν-bisimilar

[_]_≡′_ : ∀ {p q} → Size → (_ _ : ν′ S̲t̲e̲p̲ ∞ (p , q)) → Set ℓ
[_]_≡′_ = curry ∘ ν′-bisimilar

-- An alternative characterisation of bisimilarity of similarity
-- proofs.

[]≡↔ :
  Eq.Extensionality ℓ ℓ →
  ∀ {p q} {i : Size} (p≤q₁ p≤q₂ : ν S̲t̲e̲p̲ ∞ (p , q)) →

  [ i ] p≤q₁ ≡ p≤q₂

    ↔

  (∀ {p′ μ} (p⟶p′ : p [ μ ]⟶ p′) →
   let q′₁ , q⟶q′₁ , p′≤q′₁ = S̲t̲e̲p̲.challenge p≤q₁ p⟶p′
       q′₂ , q⟶q′₂ , p′≤q′₂ = S̲t̲e̲p̲.challenge p≤q₂ p⟶p′
   in ∃ λ (q′₁≡q′₂ : q′₁ ≡ q′₂) →
        subst (q [ μ ]↝_) q′₁≡q′₂ q⟶q′₁ ≡ q⟶q′₂
          ×
        [ i ] subst (ν′ S̲t̲e̲p̲ ∞ ∘ (p′ ,_)) q′₁≡q′₂ p′≤q′₁ ≡′ p′≤q′₂)

[]≡↔ ext {p} {q} {i} p≤q₁@(s₁ , f₁) p≤q₂@(s₂ , f₂) =
  [ i ] p≤q₁ ≡ p≤q₂                                                    ↝⟨ ν-bisimilar↔ ext (s₁ , f₁) (s₂ , f₂) ⟩

  (∃ λ (eq : s₁ ≡ s₂) →
   ∀ {o} (p : Container.Position S̲t̲e̲p̲ s₁ o) →
   [ i ] f₁ p ≡′ f₂ (subst (λ s → Container.Position S̲t̲e̲p̲ s o) eq p))  ↝⟨ Step.⟦S̲t̲e̲p̲⟧₂↔ ext (ν′-bisimilar i) p≤q₁ p≤q₂ ⟩□

  (∀ {p′ μ} (p⟶p′ : p [ μ ]⟶ p′) →
   let q′₁ , q⟶q′₁ , p′≤q′₁ = S̲t̲e̲p̲.challenge p≤q₁ p⟶p′
       q′₂ , q⟶q′₂ , p′≤q′₂ = S̲t̲e̲p̲.challenge p≤q₂ p⟶p′
   in ∃ λ (q′₁≡q′₂ : q′₁ ≡ q′₂) →
        subst (q [ μ ]↝_) q′₁≡q′₂ q⟶q′₁ ≡ q⟶q′₂
          ×
        [ i ] subst (ν′ S̲t̲e̲p̲ ∞ ∘ (p′ ,_)) q′₁≡q′₂ p′≤q′₁ ≡′ p′≤q′₂)    □

-- A statement of extensionality for similarity.

Extensionality : Set ℓ
Extensionality = ν′-extensionality S̲t̲e̲p̲

-- This form of extensionality can be used to derive another form (in
-- the presence of extensionality for functions).

extensionality :
  Eq.Extensionality ℓ ℓ →
  Extensionality →
  ∀ {p q} {p≤q₁ p≤q₂ : ν S̲t̲e̲p̲ ∞ (p , q)} →
  [ ∞ ] p≤q₁ ≡ p≤q₂ → p≤q₁ ≡ p≤q₂
extensionality ext ν-ext = ν-extensionality ext ν-ext
