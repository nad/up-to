------------------------------------------------------------------------
-- An up-to technique for CCS
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Bisimilarity.Up-to.CCS {Name : Set} where

open import Equality.Propositional
open import Prelude

open import Equational-reasoning
open import Labelled-transition-system

open CCS Name

import Bisimilarity.Coinductive.Equational-reasoning-instances
open import Bisimilarity.Exercises.Coinductive
open import Bisimilarity.Up-to CCS
open import Relation

-- Up to context for CCS (for polyadic contexts).

Up-to-context : ∀ {ℓ} → Trans₂ ℓ Proc
Up-to-context R (p , q) =
  ∃ λ n →
  ∃ λ (C : Context n) →
  ∃ λ ps →
  ∃ λ qs →
  p ≡ C [ ps ]
    ×
  q ≡ C [ qs ]
    ×
  ∀ x → R (ps x , qs x)

-- Up to context is an up-to technique.

Up-to-context-works :
  ∀ {ℓ} → Up-to-technique (Up-to-context {ℓ = ℓ})
Up-to-context-works = size-preserving→up-to-∀
  Up-to-context
  (λ R⊆S _ →
     Σ-map id $ Σ-map id $ Σ-map id $ Σ-map id $ Σ-map id $ Σ-map id
       (R⊆S _ ∘_))
  (λ where
    .(C [ ps ] , C [ qs ]) (_ , C , ps , qs , refl , refl , ps∼qs) →

      C [ ps ]  ∼⟨ C [ ps∼qs ]-cong ⟩■
      C [ qs ])
