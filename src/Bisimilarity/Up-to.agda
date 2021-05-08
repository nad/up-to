------------------------------------------------------------------------
-- Up-to techniques for strong bisimilarity
------------------------------------------------------------------------

{-# OPTIONS --safe --sized-types #-}

open import Labelled-transition-system

module Bisimilarity.Up-to {ℓ} (lts : LTS ℓ) where

open import Equality.Propositional
open import Logical-equivalence using (_⇔_)
open import Prelude
open import Prelude.Size

open import Bisimilarity lts
import Bisimilarity.Equational-reasoning-instances
open import Equational-reasoning
open import Relation
import Up-to

open LTS lts

------------------------------------------------------------------------
-- The general up-to machinery, instantiated with the StepC container

open Up-to StepC public

------------------------------------------------------------------------
-- Some examples (based on techniques presented by Pous and Sangiorgi
-- in "Enhancements of the bisimulation proof method")

-- Up to bisimilarity.

Up-to-bisimilarity : Trans₂ ℓ Proc
Up-to-bisimilarity R = Bisimilarity ∞ ⊙ R ⊙ Bisimilarity ∞

-- Up to bisimilarity is monotone.

up-to-bisimilarity-monotone : Monotone Up-to-bisimilarity
up-to-bisimilarity-monotone R⊆S =
  Σ-map id (Σ-map id (Σ-map id (Σ-map R⊆S id)))

-- Up to bisimilarity is size-preserving.

up-to-bisimilarity-size-preserving : Size-preserving Up-to-bisimilarity
up-to-bisimilarity-size-preserving
  R⊆∼i {p₁ , p₄} (p₂ , p₁∼p₂ , p₃ , p₂Rp₃ , p₃∼p₄) =
    p₁  ∼⟨ p₁∼p₂ ⟩
    p₂  ∼⟨ R⊆∼i p₂Rp₃ ⟩
    p₃  ∼⟨ p₃∼p₄ ⟩■
    p₄

-- Up to union with bisimilarity.

Up-to-∪∼ : Trans₂ ℓ Proc
Up-to-∪∼ R = R ∪ Bisimilarity ∞

-- Up to union with bisimilarity is monotone.

up-to-∪∼-monotone : Monotone Up-to-∪∼
up-to-∪∼-monotone R⊆S = ⊎-map R⊆S id

-- Up to union with bisimilarity is size-preserving.
--
-- The proof is similar to parts of the proof of Corollary 6.3.15 from
-- Pous and Sangiorgi's "Enhancements of the bisimulation proof
-- method".

up-to-∪∼-size-preserving : Size-preserving Up-to-∪∼
up-to-∪∼-size-preserving =
  ∪-closure
    id-size-preserving
    (const-size-preserving (Bisimilarity ∞  ⊆⟨ id ⟩∎
                            Bisimilarity ∞  ∎))

-- Up to transitive closure.

Up-to-* : Trans₂ ℓ Proc
Up-to-* R = R *

-- Up to transitive closure is monotone.

up-to-*-monotone : Monotone Up-to-*
up-to-*-monotone R⊆S = Σ-map id (λ {n} → ^^-mono R⊆S n)
  where
  ^^-mono : ∀ {R S} → R ⊆ S →
            ∀ n → R ^^ n ⊆ S ^^ n
  ^^-mono R⊆S zero    = id
  ^^-mono R⊆S (suc n) = Σ-map id (Σ-map R⊆S (^^-mono R⊆S n))

-- Up to transitive closure is size-preserving.

up-to-*-size-preserving : Size-preserving Up-to-*
up-to-*-size-preserving =
  _⇔_.from (monotone→⇔ up-to-*-monotone) drop-*
  where
  drop-* : ∀ {i} → Bisimilarity i * ⊆ Bisimilarity i
  drop-* {x = p , .p} (zero  , refl)           = p ■
  drop-* {x = p , r}  (suc n , q , p∼q , ∼ⁿqr) =
    p  ∼⟨ p∼q ⟩
    q  ∼⟨ drop-* (n , ∼ⁿqr) ⟩■
    r
