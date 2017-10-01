------------------------------------------------------------------------
-- Up-to techniques
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Labelled-transition-system

module Similarity.Weak.Up-to {ℓ} (lts : LTS ℓ) where

open import Logical-equivalence using (_⇔_)
open import Prelude

open import Equational-reasoning
open import Expansion lts using (Expansion)
open import Relation
open import Similarity.Weak lts
import Similarity.Weak.Equational-reasoning-instances
import Up-to

open LTS lts

------------------------------------------------------------------------
-- The general up-to machinery, instantiated with the StepC container

open Up-to StepC public

------------------------------------------------------------------------
-- An example

-- Up to expansion to the left and weak similarity to the right.
--
-- This is a generalisation of the non-symmetric up-to technique
-- presented by Pous and Sangiorgi in Section 6.5.2.4 of "Enhancements
-- of the bisimulation proof method".

Up-to-expansion-and-weak-similarity : Trans₂ ℓ Proc
Up-to-expansion-and-weak-similarity R =
  Expansion ∞ ⊙ R ⊙ Weak-similarity ∞

-- The relation transformer is monotone.

Up-to-expansion-and-weak-similarity-monotone :
  Monotone Up-to-expansion-and-weak-similarity
Up-to-expansion-and-weak-similarity-monotone R⊆S =
  Σ-map id (Σ-map id (Σ-map id (Σ-map R⊆S id)))

-- The relation transformer is size-preserving.

Up-to-expansion-and-weak-similarity-size-preserving :
  Size-preserving Up-to-expansion-and-weak-similarity
Up-to-expansion-and-weak-similarity-size-preserving =
  _⇔_.from (monotone→⇔ Up-to-expansion-and-weak-similarity-monotone)
    (λ where
       {x = p , q} (r , p≳r , s , r≼s , s≼q) →
         p  ∼⟨ p≳r ⟩
         r  ∼′⟨ r≼s ⟩ ≼:
         s  ∼⟨ s≼q ⟩■
         q)
