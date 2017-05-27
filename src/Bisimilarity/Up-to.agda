------------------------------------------------------------------------
-- Up-to techniques for strong bisimilarity
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

open import Labelled-transition-system

module Bisimilarity.Up-to (lts : LTS) where

open import Equality.Propositional
open import Logical-equivalence using (_⇔_)
open import Prelude

open import Bisimilarity.Coinductive lts
import Bisimilarity.Coinductive.Equational-reasoning-instances
open import Equational-reasoning
open import Relation
import Up-to

open LTS lts

------------------------------------------------------------------------
-- The general up-to machinery, instantiated with the S̲t̲e̲p̲ container

open Up-to S̲t̲e̲p̲ public

------------------------------------------------------------------------
-- Some examples

-- Up to bisimilarity.

Up-to-bisimilarity : Trans₂ (# 0) Proc
Up-to-bisimilarity R = Bisimilarity ∞ ⊙ R ⊙ Bisimilarity ∞

-- Up to bisimilarity is monotone.

Up-to-bisimilarity-monotone : Monotone Up-to-bisimilarity
Up-to-bisimilarity-monotone R⊆S =
  Σ-map id (Σ-map id (Σ-map id (Σ-map R⊆S id)))

-- Up to bisimilarity is size-preserving.
--
-- One can perhaps argue that the last part of this proof is less
-- complicated than Pous and Sangiorgi's proof of Lemma 6.3.13 in
-- "Enhancements of the bisimulation proof method". (Pous and
-- Sangiorgi seem to take for granted that the function is monotone.)

Up-to-bisimilarity-size-preserving : Size-preserving Up-to-bisimilarity
Up-to-bisimilarity-size-preserving =
  _⇔_.from (monotone→⇔ Up-to-bisimilarity-monotone)
    (λ where
       {x = p , q} (r , p∼r , s , r∼s , s∼q) →
         p  ∼⟨ p∼r ⟩
         r  ∼⟨ r∼s ⟩
         s  ∼⟨ s∼q ⟩■
         q)

-- Up to union with bisimilarity.

Up-to-∪∼ : Trans₂ (# 0) Proc
Up-to-∪∼ R = R ∪ Bisimilarity ∞

-- Up to union with bisimilarity is monotone.

Up-to-∪∼-monotone : Monotone Up-to-∪∼
Up-to-∪∼-monotone R⊆S = ⊎-map R⊆S id

-- Up to union with bisimilarity is size-preserving.
--
-- The proof is similar to parts of the proof of Pous and Sangiorgi's
-- Corollary 6.3.15.

Up-to-∪∼-size-preserving : Size-preserving Up-to-∪∼
Up-to-∪∼-size-preserving =
  ∪-closure
    id-size-preserving
    (const-size-preserving (Bisimilarity ∞  ⊆⟨ id ⟩∎
                            Bisimilarity ∞  ∎))

-- Up to transitive closure.

Up-to-* : Trans₂ (# 0) Proc
Up-to-* R = R *

-- Up to transitive closure is monotone.

Up-to-*-monotone : Monotone Up-to-*
Up-to-*-monotone R⊆S = Σ-map id (λ {n} → ^^-mono R⊆S n)
  where
  ^^-mono : ∀ {R S} → R ⊆ S →
            ∀ n → R ^^ n ⊆ S ^^ n
  ^^-mono R⊆S zero    = id
  ^^-mono R⊆S (suc n) = Σ-map id (Σ-map R⊆S (^^-mono R⊆S n))

-- Up to transitive closure is size-preserving.

Up-to-*-size-preserving : Size-preserving Up-to-*
Up-to-*-size-preserving =
  _⇔_.from (monotone→⇔ Up-to-*-monotone) drop-*
  where
  drop-* : ∀ {i} → Bisimilarity i * ⊆ Bisimilarity i
  drop-* {x = p , .p} (zero  , refl)           = p ■
  drop-* {x = p , r}  (suc n , q , p∼q , ∼ⁿqr) =
    p  ∼⟨ p∼q ⟩
    q  ∼⟨ drop-* (n , ∼ⁿqr) ⟩■
    r
