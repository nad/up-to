------------------------------------------------------------------------
-- Up-to techniques
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

open import Labelled-transition-system

module Bisimilarity.Weak.Coinductive.Other.Up-to (lts : LTS) where

open import Logical-equivalence using (_⇔_)
open import Prelude

open import Bisimilarity.Coinductive.Expansion lts
  using (Expansion; ≳:_)
import Bisimilarity.Coinductive.Expansion.Equational-reasoning-instances
open import Bisimilarity.Weak.Coinductive.Other lts
import
  Bisimilarity.Weak.Coinductive.Other.Equational-reasoning-instances
open import Equational-reasoning
open import Relation
import Up-to

open LTS lts

------------------------------------------------------------------------
-- The general up-to machinery, instantiated with the S̲t̲e̲p̲ container

open Up-to S̲t̲e̲p̲ public

------------------------------------------------------------------------
-- An example

-- Up to expansion.
--
-- I took this definition from "Enhancements of the bisimulation proof
-- method" by Pous and Sangiorgi.

Up-to-expansion : Trans₂ (# 0) Proc
Up-to-expansion R = Expansion ∞ ⊙ R ⊙ Expansion ∞ ⁻¹

-- Up to expansion is monotone.

Up-to-expansion-monotone : Monotone Up-to-expansion
Up-to-expansion-monotone R⊆S _ =
  Σ-map id (Σ-map id (Σ-map id (Σ-map (R⊆S _) id)))

-- Up to expansion is size-preserving.

Up-to-expansion-size-preserving : Size-preserving Up-to-expansion
Up-to-expansion-size-preserving =
  _⇔_.from (monotone→⇔ Up-to-expansion-monotone)
    (λ where
       (p , q) (r , p≳r , s , r≈s , s≲q) →
         p  ∼⟨ p≳r ⟩
         r  ∼′⟨ r≈s ⟩ ≳:
         s  ∽⟨ s≲q ⟩■
         q)
