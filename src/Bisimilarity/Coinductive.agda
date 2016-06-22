------------------------------------------------------------------------
-- A coinductive definition of (strong) bisimilarity
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

open import Labelled-transition-system

module Bisimilarity.Coinductive (lts : LTS) where

open import Equality.Propositional hiding (reflexive; Extensionality)
open import Prelude

import Equational-reasoning
open LTS lts

-- Bisimilarity. Note that this definition is small.

mutual

  infix 4 _∼_ _∼′_ [_]_∼_ [_]_∼′_

  record [_]_∼_ (i : Size) (p q : Proc) : Set where
    inductive
    constructor ⟨_,_⟩
    field
      left-to-right :
        ∀ {p′ μ} →
        p [ μ ]⟶ p′ → ∃ λ q′ → q [ μ ]⟶ q′ × [ i ] p′ ∼′ q′
      right-to-left :
        ∀ {q′ μ} →
        q [ μ ]⟶ q′ → ∃ λ p′ → p [ μ ]⟶ p′ × [ i ] p′ ∼′ q′

  record [_]_∼′_ (i : Size) (p q : Proc) : Set where
    coinductive
    field
      force : {j : Size< i} → [ j ] p ∼ q

open [_]_∼_  public
open [_]_∼′_ public

_∼_ : Proc → Proc → Set
p ∼ q = [ ∞ ] p ∼ q

_∼′_ : Proc → Proc → Set
p ∼′ q = [ ∞ ] p ∼′ q

-- Combinators that can perhaps make the code a bit nicer to read.

infix -3 _⟶⟨_⟩ʳˡ_ _[_]⟶⟨_⟩ʳˡ_
         lr-result-with-action lr-result-without-action

_⟶⟨_⟩ʳˡ_ : ∀ {i p′ q′ μ} p → p [ μ ]⟶ p′ → [ i ] p′ ∼′ q′ →
           ∃ λ p′ → p [ μ ]⟶ p′ × [ i ] p′ ∼′ q′
_ ⟶⟨ p⟶p′ ⟩ʳˡ p′∼′q′ = _ , p⟶p′ , p′∼′q′

_[_]⟶⟨_⟩ʳˡ_ : ∀ {i p′ q′} p μ → p [ μ ]⟶ p′ → [ i ] p′ ∼′ q′ →
              ∃ λ p′ → p [ μ ]⟶ p′ × [ i ] p′ ∼′ q′
_ [ _ ]⟶⟨ p⟶p′ ⟩ʳˡ p′∼′q′ = _ ⟶⟨ p⟶p′ ⟩ʳˡ p′∼′q′

lr-result-without-action :
  ∀ {i p′ q′ μ} → [ i ] p′ ∼′ q′ → ∀ q → q [ μ ]⟶ q′ →
  ∃ λ q′ → q [ μ ]⟶ q′ × [ i ] p′ ∼′ q′
lr-result-without-action p′∼′q′ _ q⟶q′ = _ , q⟶q′ , p′∼′q′

lr-result-with-action :
  ∀ {i p′ q′} → [ i ] p′ ∼′ q′ → ∀ μ q → q [ μ ]⟶ q′ →
  ∃ λ q′ → q [ μ ]⟶ q′ × [ i ] p′ ∼′ q′
lr-result-with-action p′∼′q′ _ _ q⟶q′ =
  lr-result-without-action  p′∼′q′ _ q⟶q′

syntax lr-result-without-action p′∼q′   q q⟶q′ = p′∼q′      ⟵⟨ q⟶q′ ⟩ q
syntax lr-result-with-action    p′∼q′ μ q q⟶q′ = p′∼q′ [ μ ]⟵⟨ q⟶q′ ⟩ q

-- Bisimilarity is an equivalence relation.

mutual

  reflexive-∼ : ∀ {p i} → [ i ] p ∼ p
  reflexive-∼ =
    ⟨ (λ p⟶p′ → _ , p⟶p′ , reflexive-∼′)
    , (λ q⟶q′ → _ , q⟶q′ , reflexive-∼′)
    ⟩

  reflexive-∼′ : ∀ {p i} → [ i ] p ∼′ p
  force reflexive-∼′ = reflexive-∼

≡⇒∼ : ∀ {p q} → p ≡ q → p ∼ q
≡⇒∼ refl = reflexive-∼

mutual

  symmetric-∼ : ∀ {i p q} → [ i ] p ∼ q → [ i ] q ∼ p
  symmetric-∼ ⟨ left-to-right , right-to-left ⟩ =
    ⟨ Σ-map id (Σ-map id symmetric-∼′) ∘ right-to-left
    , Σ-map id (Σ-map id symmetric-∼′) ∘ left-to-right
    ⟩

  symmetric-∼′ : ∀ {i p q} → [ i ] p ∼′ q → [ i ] q ∼′ p
  force (symmetric-∼′ p∼q) = symmetric-∼ (force p∼q)

mutual

  transitive-∼ : ∀ {i p q r} → [ i ] p ∼ q → [ i ] q ∼ r → [ i ] p ∼ r
  transitive-∼ {i} = λ p∼q q∼r →
    ⟨ lr p∼q q∼r
    , Σ-map id (Σ-map id symmetric-∼′) ∘
      lr (symmetric-∼ q∼r) (symmetric-∼ p∼q)
    ⟩
    where
    lr : ∀ {p p′ q r μ} →
         [ i ] p ∼ q → [ i ] q ∼ r → p [ μ ]⟶ p′ →
         ∃ λ r′ → r [ μ ]⟶ r′ × [ i ] p′ ∼′ r′
    lr p∼q q∼r p⟶p′ =
      let q′ , q⟶q′ , p′∼q′ = left-to-right p∼q p⟶p′
          r′ , r⟶r′ , q′∼r′ = left-to-right q∼r q⟶q′
      in r′ , r⟶r′ , transitive-∼′ p′∼q′ q′∼r′

  transitive-∼′ :
    ∀ {i p q r} → [ i ] p ∼′ q → [ i ] q ∼′ r → [ i ] p ∼′ r
  force (transitive-∼′ p∼q q∼r) = transitive-∼ (force p∼q) (force q∼r)

-- Functions that can be used to aid the instance resolution
-- mechanism.

infix -2 ∼:_ ∼′:_

∼:_ : ∀ {i p q} → [ i ] p ∼ q → [ i ] p ∼ q
∼:_ = id

∼′:_ : ∀ {i p q} → [ i ] p ∼′ q → [ i ] p ∼′ q
∼′:_ = id

-- Strong bisimilarity is a weak bisimulation (of a certain kind).

strong-is-weak :
  ∀ {p p′ q μ} →
  p ∼ q → p [ μ ]⇒̂ p′ →
  ∃ λ q′ → q [ μ ]⇒̂ q′ × p′ ∼ q′
strong-is-weak =
  is-weak left-to-right (λ p∼′q → force p∼′q)
          (λ s tr → step s tr done) ⟶→⇒̂

-- Bisimilarity of bisimilarity proofs.
--
-- TODO: Define in a less monolithic way?

mutual

  infix 4 [_]_≡_ [_]_≡′_

  record [_]_≡_ (i : Size) {p q : Proc}
                (p∼q₁ p∼q₂ : p ∼ q) : Set where
    inductive
    constructor ⟨_,_⟩
    field
      left-to-right :
        ∀ {p′ μ} (p⟶p′ : p [ μ ]⟶ p′) →
        let q′₁ , q⟶q′₁ , p′∼q′₁ = left-to-right p∼q₁ p⟶p′
            q′₂ , q⟶q′₂ , p′∼q′₂ = left-to-right p∼q₂ p⟶p′
        in ∃ λ (q′₁≡q′₂ : q′₁ ≡ q′₂) →
             subst (q [ μ ]⟶_) q′₁≡q′₂ q⟶q′₁ ≡ q⟶q′₂
               ×
             [ i ] subst (p′ ∼_) q′₁≡q′₂ (force p′∼q′₁) ≡′ force p′∼q′₂
      right-to-left :
        ∀ {q′ μ} (q⟶q′ : q [ μ ]⟶ q′) →
        let p′₁ , p⟶p′₁ , p′∼q′₁ = right-to-left p∼q₁ q⟶q′
            p′₂ , p⟶p′₂ , p′∼q′₂ = right-to-left p∼q₂ q⟶q′
        in ∃ λ (p′₁≡p′₂ : p′₁ ≡ p′₂) →
             subst (p [ μ ]⟶_) p′₁≡p′₂ p⟶p′₁ ≡ p⟶p′₂
               ×
             [ i ] subst (_∼ q′) p′₁≡p′₂ (force p′∼q′₁) ≡′ force p′∼q′₂

  record [_]_≡′_ (i : Size) {p q : Proc}
                 (p∼q₁ p∼q₂ : p ∼ q) : Set where
    coinductive
    field
      force : {j : Size< i} → [ j ] p∼q₁ ≡ p∼q₂

open [_]_≡_  public
open [_]_≡′_ public

-- A statement of extensionality for bisimilarity.

Extensionality : Set
Extensionality =
  ∀ {p q} {p∼q₁ p∼q₂ : p ∼ q} →
  [ ∞ ] p∼q₁ ≡ p∼q₂ → p∼q₁ ≡ p∼q₂
