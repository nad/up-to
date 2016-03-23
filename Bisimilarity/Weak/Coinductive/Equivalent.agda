------------------------------------------------------------------------
-- The two coinductive definitions of weak bisimilarity are logically
-- equivalent
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

open import Labelled-transition-system

module Bisimilarity.Weak.Coinductive.Equivalent {lts : LTS} where

open import Equality.Propositional
open import Logical-equivalence using (_⇔_)
open import Prelude

import Bisimilarity.Weak.Coinductive       lts as CW
import Bisimilarity.Weak.Coinductive.Other lts as CWO

open LTS lts

mutual

  -- One kind of weak bisimilarity can be converted to another, in a
  -- size-preserving way.

  cw⇒cwo : ∀ {i p q} → CW.[ i ] p ≈ q → CWO.[ i ] p ≈ q
  cw⇒cwo p≈q =
    CWO.⟨ lr p≈q
        , Σ-map id (Σ-map id CWO.symmetric-≈′) ∘ lr (CW.symmetric p≈q)
        ⟩
    where
    lr : ∀ {i p p′ q μ} →
         CW.[ i ] p ≈ q → p [ μ ]⟶ p′ →
         ∃ λ q′ → q [ μ ]⇒̂ q′ × CWO.[ i ] p′ ≈′ q′
    lr p≈q p⟶p′ =
      Σ-map id (Σ-map id cw⇒cwo′)
        (CW.[_]_≈_.left-to-right p≈q (⟶→⇒̂ p⟶p′))

  cw⇒cwo′ : ∀ {i p q} → CW.[ i ] p ≈′ q → CWO.[ i ] p ≈′ q
  CWO.[_]_≈′_.force (cw⇒cwo′ p≈′q) = cw⇒cwo (CW.[_]_≈′_.force p≈′q)

mutual

  -- One can also convert in the other direction. Note that this
  -- conversion is not size-preserving.

  -- TODO: Can one prove that the conversion cannot be
  -- size-preserving?

  cwo⇒cw : ∀ {i p q} → p CWO.≈ q → CW.[ i ] p ≈ q
  cwo⇒cw p≈q =
    CW.⟨ lr p≈q
       , Σ-map id (Σ-map id CW.symmetric′) ∘ lr (CWO.symmetric-≈ p≈q)
       ⟩
    where
    lr : ∀ {i p p′ q μ} →
         p CWO.≈ q → p [ μ ]⇒̂ p′ →
         ∃ λ q′ → q [ μ ]⇒̂ q′ × CW.[ i ] p′ ≈′ q′
    lr p≈q p⇒̂p′ =
      Σ-map id (Σ-map id cwo⇒cw′) (CWO.weak-is-weak p≈q p⇒̂p′)

  cwo⇒cw′ : ∀ {i p q} → p CWO.≈ q → CW.[ i ] p ≈′ q
  CW.[_]_≈′_.force (cwo⇒cw′ p≈q) = cwo⇒cw p≈q

-- The two definitions of weak bisimilarity are logically equivalent.

cw⇔cwo : ∀ {p q} → p CW.≈ q ⇔ p CWO.≈ q
cw⇔cwo = record
  { to   = cw⇒cwo
  ; from = cwo⇒cw
  }

-- TODO: I don't know if the two definitions of weak bisimilarity are
-- isomorphic.
