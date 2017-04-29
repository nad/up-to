------------------------------------------------------------------------
-- An up-to technique for CCS
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Bisimilarity.Up-to.CCS {Name : Set} where

open import Equality.Propositional
open import Logical-equivalence using (_⇔_)
open import Prelude

open import Equational-reasoning
open import Labelled-transition-system

open CCS Name

import Bisimilarity.Coinductive.Equational-reasoning-instances
open import Bisimilarity.Exercises.Coinductive
open import Bisimilarity.Up-to CCS
open import Relation

-- Up to context for CCS (for polyadic contexts).

Up-to-context : Trans₂ (# 0) Proc
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

-- Up to context is monotone.

Up-to-context-monotone : Monotone Up-to-context
Up-to-context-monotone R⊆S _ =
  Σ-map id $ Σ-map id $ Σ-map id $ Σ-map id $ Σ-map id $ Σ-map id
    (R⊆S _ ∘_)

-- Up to context is size-preserving.

Up-to-context-size-preserving : Size-preserving Up-to-context
Up-to-context-size-preserving =
  _⇔_.from (monotone→⇔ Up-to-context-monotone)
  (λ where
    .(C [ ps ] , C [ qs ]) (_ , C , ps , qs , refl , refl , ps∼qs) →

      C [ ps ]  ∼⟨ C [ ps∼qs ]-cong ⟩■
      C [ qs ])
