------------------------------------------------------------------------
-- A coinductive definition of (strong) bisimilarity
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Labelled-transition-system

module Bisimilarity.Coinductive {ℓ} (lts : LTS ℓ) where

open import Prelude

import Bisimilarity.Coinductive.General
open import Relation

open LTS lts

private
  module General =
    Bisimilarity.Coinductive.General lts _[_]⟶_ _[_]⟶_ id id

open General public
  hiding (Bisimilarity; Bisimilarity′; [_]_∼_; [_]_∼′_; _∼_; _∼′_)

-- Some definitions are given in the following way, rather than via
-- open public, to make hyperlinks to these definitions more
-- informative.

Bisimilarity : Size → Rel₂ ℓ Proc
Bisimilarity = General.Bisimilarity

Bisimilarity′ : Size → Rel₂ ℓ Proc
Bisimilarity′ = General.Bisimilarity′

infix 4 _∼_ _∼′_ [_]_∼_ [_]_∼′_

[_]_∼_ : Size → Proc → Proc → Set ℓ
[_]_∼_ = General.[_]_∼_

[_]_∼′_ : Size → Proc → Proc → Set ℓ
[_]_∼′_ = General.[_]_∼′_

_∼_ : Proc → Proc → Set ℓ
_∼_ = General._∼_

_∼′_ : Proc → Proc → Set ℓ
_∼′_ = General._∼′_

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

-- Strong bisimilarity is a weak simulation (of a certain kind).

strong-is-weak :
  ∀ {p p′ q μ} →
  p ∼ q → p [ μ ]⇒̂ p′ →
  ∃ λ q′ → q [ μ ]⇒̂ q′ × p′ ∼ q′
strong-is-weak =
  is-weak StepC.left-to-right (λ p∼′q → force p∼′q)
          (λ s tr → step s tr done) ⟶→⇒̂

mutual

  -- Bisimilarity is symmetric.

  symmetric-∼ : ∀ {i p q} → [ i ] p ∼ q → [ i ] q ∼ p
  symmetric-∼ p∼q =
    StepC.⟨ Σ-map id (Σ-map id symmetric-∼′) ∘ StepC.right-to-left p∼q
          , Σ-map id (Σ-map id symmetric-∼′) ∘ StepC.left-to-right p∼q
          ⟩

  symmetric-∼′ : ∀ {i p q} → [ i ] p ∼′ q → [ i ] q ∼′ p
  force (symmetric-∼′ p∼q) = symmetric-∼ (force p∼q)

mutual

  -- Strong bisimilarity is transitive.

  transitive-∼ : ∀ {i p q r} → [ i ] p ∼ q → [ i ] q ∼ r → [ i ] p ∼ r
  transitive-∼ {i} = λ p∼q q∼r →
    StepC.⟨ lr p∼q q∼r
          , Σ-map id (Σ-map id symmetric-∼′) ∘
            lr (symmetric-∼ q∼r) (symmetric-∼ p∼q)
          ⟩
    where
    lr : ∀ {p p′ q r μ} →
         [ i ] p ∼ q → [ i ] q ∼ r → p [ μ ]⟶ p′ →
         ∃ λ r′ → r [ μ ]⟶ r′ × [ i ] p′ ∼′ r′
    lr p∼q q∼r p⟶p′ =
      let q′ , q⟶q′ , p′∼q′ = StepC.left-to-right p∼q p⟶p′
          r′ , r⟶r′ , q′∼r′ = StepC.left-to-right q∼r q⟶q′
      in r′ , r⟶r′ , transitive-∼′ p′∼q′ q′∼r′

  transitive-∼′ :
    ∀ {i p q r} → [ i ] p ∼′ q → [ i ] q ∼′ r → [ i ] p ∼′ r
  force (transitive-∼′ p∼q q∼r) = transitive-∼ (force p∼q) (force q∼r)
