------------------------------------------------------------------------
-- A coinductive definition of (strong) bisimilarity
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

open import Labelled-transition-system

module Bisimilarity.Coinductive (lts : LTS) where

open import Prelude

open LTS lts

open import Bisimilarity.Coinductive.General
              lts _[_]⟶_ _[_]⟶_ id id public

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
  is-weak S̲t̲e̲p̲.left-to-right (λ p∼′q → force p∼′q)
          (λ s tr → step s tr done) ⟶→⇒̂

mutual

  -- Bisimilarity is symmetric.

  symmetric-∼ : ∀ {i p q} → [ i ] p ∼ q → [ i ] q ∼ p
  symmetric-∼ p∼q =
    S̲t̲e̲p̲.⟨ Σ-map id (Σ-map id symmetric-∼′) ∘ S̲t̲e̲p̲.right-to-left p∼q
         , Σ-map id (Σ-map id symmetric-∼′) ∘ S̲t̲e̲p̲.left-to-right p∼q
         ⟩

  symmetric-∼′ : ∀ {i p q} → [ i ] p ∼′ q → [ i ] q ∼′ p
  force (symmetric-∼′ p∼q) = symmetric-∼ (force p∼q)

mutual

  -- Strong bisimilarity is transitive.

  transitive-∼ : ∀ {i p q r} → [ i ] p ∼ q → [ i ] q ∼ r → [ i ] p ∼ r
  transitive-∼ {i} = λ p∼q q∼r →
    S̲t̲e̲p̲.⟨ lr p∼q q∼r
         , Σ-map id (Σ-map id symmetric-∼′) ∘
           lr (symmetric-∼ q∼r) (symmetric-∼ p∼q)
         ⟩
    where
    lr : ∀ {p p′ q r μ} →
         [ i ] p ∼ q → [ i ] q ∼ r → p [ μ ]⟶ p′ →
         ∃ λ r′ → r [ μ ]⟶ r′ × [ i ] p′ ∼′ r′
    lr p∼q q∼r p⟶p′ =
      let q′ , q⟶q′ , p′∼q′ = S̲t̲e̲p̲.left-to-right p∼q p⟶p′
          r′ , r⟶r′ , q′∼r′ = S̲t̲e̲p̲.left-to-right q∼r q⟶q′
      in r′ , r⟶r′ , transitive-∼′ p′∼q′ q′∼r′

  transitive-∼′ :
    ∀ {i p q r} → [ i ] p ∼′ q → [ i ] q ∼′ r → [ i ] p ∼′ r
  force (transitive-∼′ p∼q q∼r) = transitive-∼ (force p∼q) (force q∼r)
