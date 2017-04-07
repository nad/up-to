------------------------------------------------------------------------
-- The Step function, used to define bisimilarity
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

open import Labelled-transition-system

module Bisimilarity.Step (lts : LTS) where

open import Prelude

open import Bisimilarity.Classical.Preliminaries

open LTS lts

-- This is basically the function from Definition 6.3.1 in Pous and
-- Sangiorgi's "Enhancements of the bisimulation proof method", except
-- that clause (3) is omitted.

record Step {r} (_R_ : Rel r Proc) (p q : Proc) : Set r where
  constructor ⟨_,_⟩
  field
    left-to-right : ∀ {p′ μ} →
                    p [ μ ]⟶ p′ → ∃ λ q′ → q [ μ ]⟶ q′ × p′ R q′
    right-to-left : ∀ {q′ μ} →
                    q [ μ ]⟶ q′ → ∃ λ p′ → p [ μ ]⟶ p′ × p′ R q′

-- Step is monotone.

Step-monotone : ∀ {ℓ₁ ℓ₂} → Monotone-∀ Step ℓ₁ ℓ₂
Step-monotone R⊆S p q StepRpq =
  ⟨ (λ p⟶p′ → Σ-map id (Σ-map id (R⊆S _ _))
                (Step.left-to-right StepRpq p⟶p′))
  , (λ q⟶q′ → Σ-map id (Σ-map id (R⊆S _ _))
                (Step.right-to-left StepRpq q⟶q′))
  ⟩
