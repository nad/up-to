------------------------------------------------------------------------
-- Up-to techniques
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

open import Labelled-transition-system

module Bisimilarity.Up-to (lts : LTS) where

open import Equality.Propositional
open import Prelude

open import Bisimilarity.Coinductive lts
import Bisimilarity.Coinductive.Equational-reasoning-instances
open import Equational-reasoning
open import Relation
open import Up-to S̲t̲e̲p̲ public

open LTS lts

------------------------------------------------------------------------
-- Some examples

-- Up to bisimilarity.

Up-to-bisimilarity : Trans₂ (# 0) Proc
Up-to-bisimilarity R = Bisimilarity ∞ ⊙ R ⊙ Bisimilarity ∞

-- Up to bisimilarity is an up-to technique.
--
-- One can perhaps argue that the second part of this proof is less
-- complicated than Pous and Sangiorgi's proof of Lemma 6.3.13 in
-- "Enhancements of the bisimulation proof method". (Pous and
-- Sangiorgi seem to take for granted that the function is monotone.)

Up-to-bisimilarity-works : Up-to-technique Up-to-bisimilarity
Up-to-bisimilarity-works = size-preserving→up-to′
  (λ R⊆S _ → Σ-map id (Σ-map id (Σ-map id (Σ-map (R⊆S _) id))))
  (λ where
     (p , q) (r , p∼r , s , r∼s , s∼q) →
       p  ∼⟨ p∼r ⟩
       r  ∼⟨ r∼s ⟩
       s  ∼⟨ s∼q ⟩■
       q)

-- Up to union with bisimilarity.

Up-to-∪∼ : Trans₂ (# 0) Proc
Up-to-∪∼ R = R ∪ Bisimilarity ∞

-- Up to union with bisimilarity is an up-to technique.

Up-to-∪∼-works : Up-to-technique Up-to-∪∼
Up-to-∪∼-works = size-preserving→up-to′
  (λ R⊆S _ → ⊎-map (R⊆S _) id)
  (λ where
     (p , q) (inj₁ p∼q) → p  ∼⟨ p∼q ⟩■
                          q
     (p , q) (inj₂ p∼q) → p  ∼⟨ p∼q ⟩■
                          q)

-- Up to transitive closure.

Up-to-* : Trans₂ (# 0) Proc
Up-to-* R = R *

-- Up to transitive closure is an up-to technique.

Up-to-*-works : Up-to-technique Up-to-*
Up-to-*-works = size-preserving→up-to′
  (λ R⊆S _ → Σ-map id (λ {n} → ^^-mono R⊆S n _))
  drop-*
  where
  ^^-mono : ∀ {R S} → R ⊆ S →
            ∀ n → R ^^ n ⊆ S ^^ n
  ^^-mono R⊆S zero    _ = id
  ^^-mono R⊆S (suc n) _ =
    Σ-map id (Σ-map (R⊆S _) (^^-mono R⊆S n _))

  drop-* : ∀ {i} pq → (Bisimilarity i *) pq → Bisimilarity i pq
  drop-* (p , .p) (zero  , refl)           = p ■
  drop-* (p , r)  (suc n , q , p∼q , ∼ⁿqr) =
    p  ∼⟨ p∼q ⟩
    q  ∼⟨ drop-* _ (n , ∼ⁿqr) ⟩■
    r
