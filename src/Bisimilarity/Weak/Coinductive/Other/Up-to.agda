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
-- Up to expansion

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

------------------------------------------------------------------------
-- Up to weak bisimilarity

-- Up to weak bisimilarity.
--
-- I based this definition on Definition 4.2.13 in Milner's
-- "Operational and Algebraic Semantics of Concurrent Processes".

Up-to-weak-bisimilarity : Trans₂ ℓ Proc
Up-to-weak-bisimilarity R =
  Weak-bisimilarity ∞ ⊙ R ⊙ Weak-bisimilarity ∞

-- Up to weak bisimilarity is monotone.

up-to-weak-bisimilarity-monotone : Monotone Up-to-weak-bisimilarity
up-to-weak-bisimilarity-monotone R⊆S =
  Σ-map id (Σ-map id (Σ-map id (Σ-map R⊆S id)))

-- If transitivity of weak bisimilarity is size-preserving in the
-- first argument, then "up to weak bisimilarity" is size-preserving.

size-preserving-transitivity→up-to-weak-bisimilarity-size-preserving :
  (∀ {i x y z} → [ i ] x ≈ y → [ ∞ ] y ≈ z → [ i ] x ≈ z) →
  Size-preserving Up-to-weak-bisimilarity
size-preserving-transitivity→up-to-weak-bisimilarity-size-preserving
  trans =
  _⇔_.from (monotone→⇔ up-to-weak-bisimilarity-monotone) λ where
    {x = p , q} (r , p≈r , s , r≈s , s≈q) →
      p  ≈∞⟨ p≈r ⟩
      r  ≈⟨ r≈s ⟩∞
      s  ∼⟨ s≈q ⟩■
      q
  where
  infixr -2 _≈⟨_⟩∞_ _≈∞⟨_⟩_

  _≈⟨_⟩∞_ : ∀ {i} x {y z} → [ i ] x ≈ y → [ ∞ ] y ≈ z → [ i ] x ≈ z
  _ ≈⟨ p ⟩∞ q = trans p q

  _≈∞⟨_⟩_ : ∀ {i} x {y z} → [ ∞ ] x ≈ y → [ i ] y ≈ z → [ i ] x ≈ z
  _ ≈∞⟨ p ⟩ q = symmetric (trans (symmetric q) (symmetric p))

-- If transitivity of weak bisimilarity is size-preserving in both
-- arguments, then weak bisimulations up to weak bisimilarity are
-- contained in weak bisimilarity.

size-preserving-transitivity→up-to-weak-bisimilarity-up-to :
  (∀ {i x y z} → [ i ] x ≈ y → [ i ] y ≈ z → [ i ] x ≈ z) →
  Up-to-technique Up-to-weak-bisimilarity
size-preserving-transitivity→up-to-weak-bisimilarity-up-to =
  size-preserving→up-to ∘
  size-preserving-transitivity→up-to-weak-bisimilarity-size-preserving
