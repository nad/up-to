------------------------------------------------------------------------
-- Up-to techniques
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
open import Up-to S̲t̲e̲p̲ public

open LTS lts

------------------------------------------------------------------------
-- Some examples

-- Up to bisimilarity.

Up-to-bisimilarity : Trans₂ (# 0) Proc
Up-to-bisimilarity R = Bisimilarity ∞ ⊙ R ⊙ Bisimilarity ∞

-- Up to bisimilarity is monotone.

Up-to-bisimilarity-monotone : Monotone Up-to-bisimilarity
Up-to-bisimilarity-monotone R⊆S _ =
  Σ-map id (Σ-map id (Σ-map id (Σ-map (R⊆S _) id)))

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
       (p , q) (r , p∼r , s , r∼s , s∼q) →
         p  ∼⟨ p∼r ⟩
         r  ∼⟨ r∼s ⟩
         s  ∼⟨ s∼q ⟩■
         q)

-- Up to union with bisimilarity.

Up-to-∪∼ : Trans₂ (# 0) Proc
Up-to-∪∼ R = R ∪ Bisimilarity ∞

-- Up to union with bisimilarity is monotone.

Up-to-∪∼-monotone : Monotone Up-to-∪∼
Up-to-∪∼-monotone R⊆S _ = ⊎-map (R⊆S _) id

-- Up to union with bisimilarity is size-preserving.

Up-to-∪∼-size-preserving : Size-preserving Up-to-∪∼
Up-to-∪∼-size-preserving =
  _⇔_.from (monotone→⇔ Up-to-∪∼-monotone)
    (λ where
       (p , q) (inj₁ p∼q) → p  ∼⟨ p∼q ⟩■
                            q
       (p , q) (inj₂ p∼q) → p  ∼⟨ p∼q ⟩■
                            q)

-- Up to transitive closure.

Up-to-* : Trans₂ (# 0) Proc
Up-to-* R = R *

-- Up to transitive closure is monotone.

Up-to-*-monotone : Monotone Up-to-*
Up-to-*-monotone R⊆S _ = Σ-map id (λ {n} → ^^-mono R⊆S n _)
  where
  ^^-mono : ∀ {R S} → R ⊆ S →
            ∀ n → R ^^ n ⊆ S ^^ n
  ^^-mono R⊆S zero    _ = id
  ^^-mono R⊆S (suc n) _ =
    Σ-map id (Σ-map (R⊆S _) (^^-mono R⊆S n _))

-- Up to transitive closure is size-preserving.

Up-to-*-size-preserving : Size-preserving Up-to-*
Up-to-*-size-preserving =
  _⇔_.from (monotone→⇔ Up-to-*-monotone) drop-*
  where
  drop-* : ∀ {i} → Bisimilarity i * ⊆ Bisimilarity i
  drop-* (p , .p) (zero  , refl)           = p ■
  drop-* (p , r)  (suc n , q , p∼q , ∼ⁿqr) =
    p  ∼⟨ p∼q ⟩
    q  ∼⟨ drop-* _ (n , ∼ⁿqr) ⟩■
    r
