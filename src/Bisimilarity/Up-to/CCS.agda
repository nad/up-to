------------------------------------------------------------------------
-- An up-to technique for CCS
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Bisimilarity.Up-to.CCS {Name : Set} where

open import Equality.Propositional
open import Logical-equivalence using (_⇔_)
open import Prelude

open import Bijection equality-with-J using (_↔_)
open import Function-universe equality-with-J hiding (id; _∘_)

import Bisimilarity.Coinductive.Equational-reasoning-instances
open import Bisimilarity.Exercises.Coinductive.CCS
  using (_[_]-cong; 6-1-3-2; ≡→∼)
open import Equational-reasoning
open import Indexed-container
open import Labelled-transition-system.CCS Name
open import Relation

open import Bisimilarity.Coinductive CCS
open import Bisimilarity.Exercises.Coinductive.CCS
open import Bisimilarity.Step CCS _[_]⟶_ using (Step; Step↔S̲t̲e̲p̲)
open import Bisimilarity.Up-to CCS

-- Up to context for a very simple kind of context.

Up-to-!-context : Trans₂ (# 0) (Proc ∞)
Up-to-!-context R (P , Q) =
  ∃ λ P′ → ∃ λ Q′ → P ≡ ! P′ × R (P′ , Q′) × ! Q′ ≡ Q

-- This transformer is size-preserving.

Up-to-!-context-size-preserving : Size-preserving Up-to-!-context
Up-to-!-context-size-preserving
  {R = R} {i = i} R⊆∼ (P′ , Q′ , refl , P′RQ′ , refl) =

                     $⟨ P′RQ′ ⟩
  R (P′ , Q′)        ↝⟨ R⊆∼ ⟩
  [ i ] P′ ∼ Q′      ↝⟨ !-cong_ ⟩□
  [ i ] ! P′ ∼ ! Q′  □

-- Up to context for CCS (for polyadic contexts).

Up-to-context : Trans₂ (# 0) (Proc ∞)
Up-to-context R (p , q) =
  ∃ λ n →
  ∃ λ (C : Context ∞ n) →
  ∃ λ ps →
  ∃ λ qs →
  Equal ∞ p (C [ ps ])
    ×
  Equal ∞ q (C [ qs ])
    ×
  ∀ x → R (ps x , qs x)

-- Up to context is monotone.

Up-to-context-monotone : Monotone Up-to-context
Up-to-context-monotone R⊆S =
  Σ-map id $ Σ-map id $ Σ-map id $ Σ-map id $ Σ-map id $ Σ-map id
    (R⊆S ∘_)

-- Up to context is size-preserving.

Up-to-context-size-preserving : Size-preserving Up-to-context
Up-to-context-size-preserving =
  _⇔_.from (monotone→⇔ Up-to-context-monotone)
  (λ where
     {x = p , q} (_ , C , ps , qs , eq₁ , eq₂ , ps∼qs) →

       p         ∼⟨ ≡→∼ eq₁ ⟩
       C [ ps ]  ∼⟨ C [ ps∼qs ]-cong ⟩
       C [ qs ]  ∼⟨ symmetric (≡→∼ eq₂) ⟩■
       q)
