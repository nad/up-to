------------------------------------------------------------------------
-- Up-to techniques for the "other" definition of weak bisimilarity
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Labelled-transition-system

module Bisimilarity.Weak.Coinductive.Other.Up-to
         {ℓ} (lts : LTS ℓ) where

open import Logical-equivalence using (_⇔_)
open import Prelude

open import Bisimilarity.Weak.Coinductive.Other lts
import
  Bisimilarity.Weak.Coinductive.Other.Equational-reasoning-instances
open import Equational-reasoning
open import Expansion lts using (Expansion; ≳:_)
import Expansion.Equational-reasoning-instances
open import Relation
import Up-to

open LTS lts

------------------------------------------------------------------------
-- The general up-to machinery, instantiated with the StepC container

open Up-to StepC public

------------------------------------------------------------------------
-- An example

-- Up to expansion.
--
-- I took this definition from "Enhancements of the bisimulation proof
-- method" by Pous and Sangiorgi.

Up-to-expansion : Trans₂ ℓ Proc
Up-to-expansion R = Expansion ∞ ⊙ R ⊙ Expansion ∞ ⁻¹

-- Up to expansion is monotone.

up-to-expansion-monotone : Monotone Up-to-expansion
up-to-expansion-monotone R⊆S =
  Σ-map id (Σ-map id (Σ-map id (Σ-map R⊆S id)))

-- Up to expansion is size-preserving.

up-to-expansion-size-preserving : Size-preserving Up-to-expansion
up-to-expansion-size-preserving =
  _⇔_.from (monotone→⇔ up-to-expansion-monotone)
    (λ where
       {x = p , q} (r , p≳r , s , r≈s , s≲q) →
         p  ∼⟨ p≳r ⟩
         r  ∼′⟨ r≈s ⟩ ≳:
         s  ∽⟨ s≲q ⟩■
         q)
