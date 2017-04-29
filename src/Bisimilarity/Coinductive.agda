------------------------------------------------------------------------
-- A coinductive definition of (strong) bisimilarity
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

open import Labelled-transition-system

module Bisimilarity.Coinductive (lts : LTS) where

open import Prelude

open LTS lts

open import Bisimilarity.Coinductive.General lts _[_]⟶_ id public

-- Strong bisimilarity is a weak bisimulation (of a certain kind).

strong-is-weak :
  ∀ {p p′ q μ} →
  p ∼ q → p [ μ ]⇒̂ p′ →
  ∃ λ q′ → q [ μ ]⇒̂ q′ × p′ ∼ q′
strong-is-weak =
  is-weak S̲t̲e̲p̲.left-to-right (λ p∼′q → force p∼′q)
          (λ s tr → step s tr done) ⟶→⇒̂

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
