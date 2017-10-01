------------------------------------------------------------------------
-- The two coinductive definitions of weak bisimilarity are pointwise
-- logically equivalent
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Labelled-transition-system

module Bisimilarity.Weak.Coinductive.Equivalent {ℓ} {lts : LTS ℓ} where

open import Equality.Propositional
open import Logical-equivalence using (_⇔_)
open import Prelude

import Bisimilarity.Weak.Coinductive lts as CW
import Bisimilarity.Weak.Coinductive.Equational-reasoning-instances
import Bisimilarity.Weak.Coinductive.Other lts as CWO
import
  Bisimilarity.Weak.Coinductive.Other.Equational-reasoning-instances
open import Equational-reasoning

open LTS lts

mutual

  -- One kind of weak bisimilarity can be converted to another, in a
  -- size-preserving way.

  cw⇒cwo : ∀ {i p q} → CW.[ i ] p ≈ q → CWO.[ i ] p ≈ q
  cw⇒cwo p≈q =
    CWO.⟨ lr p≈q
        , Σ-map id (Σ-map id symmetric) ∘ lr (symmetric p≈q)
        ⟩
    where
    lr : ∀ {i p p′ q μ} →
         CW.[ i ] p ≈ q → p [ μ ]⟶ p′ →
         ∃ λ q′ → q [ μ ]⇒̂ q′ × CWO.[ i ] p′ ≈′ q′
    lr p≈q p⟶p′ =
      Σ-map id (Σ-map id cw⇒cwo′) (CW.left-to-right p≈q (⟶→⇒̂ p⟶p′))

  cw⇒cwo′ : ∀ {i p q} → CW.[ i ] p ≈′ q → CWO.[ i ] p ≈′ q
  CWO.force (cw⇒cwo′ p≈′q) = cw⇒cwo (CW.force p≈′q)

mutual

  -- One can also convert in the other direction. Note that this
  -- conversion is not guaranteed to be size-preserving. For at least
  -- one LTS it cannot (in general) be size-preserving, see
  -- Bisimilarity.Weak.Delay-monad.size-preserving-cwo⇒cw⇔uninhabited.

  cwo⇒cw : ∀ {i p q} → p CWO.≈ q → CW.[ i ] p ≈ q
  cwo⇒cw {i} p≈q =
    CW.⟨ lr p≈q
       , Σ-map id (Σ-map id symmetric) ∘ lr (symmetric p≈q)
       ⟩
    where
    lr : ∀ {p p′ q μ} →
         p CWO.≈ q → p [ μ ]⇒̂ p′ →
         ∃ λ q′ → q [ μ ]⇒̂ q′ × CW.[ i ] p′ ≈′ q′
    lr p≈q p⇒̂p′ =
      Σ-map id (Σ-map id cwo⇒cw′) (CWO.weak-is-weak p≈q p⇒̂p′)

  cwo⇒cw′ : ∀ {i p q} → p CWO.≈ q → CW.[ i ] p ≈′ q
  CW.force (cwo⇒cw′ p≈q) = cwo⇒cw p≈q

-- The two definitions of weak bisimilarity are logically equivalent.

cw⇔cwo : ∀ {p q} → p CW.≈ q ⇔ p CWO.≈ q
cw⇔cwo = record
  { to   = cw⇒cwo
  ; from = cwo⇒cw
  }

-- TODO: I don't know if the two definitions of weak bisimilarity are
-- isomorphic.
