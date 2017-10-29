------------------------------------------------------------------------
-- An example that requires names to be natural numbers
--
-- Implemented using the coinductive definition of bisimilarity.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Bisimilarity.Exercises.Coinductive.CCS.Natural-numbers where

open import Equality.Propositional
open import Prelude

import Bisimilarity.Coinductive.Equational-reasoning-instances
open import Bisimilarity.Exercises.Coinductive.CCS
open import Equational-reasoning
open import Labelled-transition-system.CCS ℕ

open import Bisimilarity.Coinductive CCS

module _ (μ : Action) where

  P : ∀ {i} → ℕ → Proc i
  P n = Restricted n ∣ (μ · λ { .force → P (1 + n) })

  Q : ∀ {i} → Proc i
  Q = μ · λ { .force → Q }

  P∼Q : ∀ {i n} → [ i ] P n ∼ Q
  P∼Q {n = n} =
    P n    ∼⟨ Restricted∼∅ ∣-cong (refl ·-cong λ { .force → P∼Q }) ⟩
    ∅ ∣ Q  ∼⟨ ∣-left-identity ⟩■
    Q
