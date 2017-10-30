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
open import Expansion lts as E using (Expansion; _≲_; ≳:_)
import Expansion.Equational-reasoning-instances
open import Indexed-container
open import Relation
import Similarity.Weak lts as S
import Up-to

open LTS lts

import Similarity.Step lts _[_]⇒̂_ as SS

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
-- A generalisation of up to expansion

mutual

  -- A monolithic implementation of a non-symmetric variant of up to
  -- expansion, based on the technique presented in Section 6.5.2.4 of
  -- "Enhancements of the bisimulation proof method" by Pous and
  -- Sangiorgi.
  --
  -- It is at the time of writing not clear to me if there is some
  -- size-preserving proof that matches this technique.

  6-5-2-4 :
    {R : Rel₂ ℓ Proc} →
    (∀ {P P′ Q μ} →
     R (P , Q) → P [ μ ]⟶ P′ →
     ∃ λ Q′ → Q [ μ ]⇒̂ Q′ ×
       (Expansion ∞ ⊙ R ⊙ Weak-bisimilarity ∞) (P′ , Q′)) →
    (∀ {P Q Q′ μ} →
     R (P , Q) → Q [ μ ]⟶ Q′ →
     ∃ λ P′ → P [ μ ]⇒̂ P′ ×
       (Weak-bisimilarity ∞ ⊙ R ⊙ Expansion ∞ ⁻¹) (P′ , Q′)) →
    R ⊆ Weak-bisimilarity ∞
  6-5-2-4 {R} lr⟶ rl⟶ =
    6-5-2-4′ (λ PRQ → S.⟨ lr⟶ PRQ ⟩)
             (λ PR⁻¹Q → S.⟨ Σ-map id (Σ-map id lemma) ∘ rl⟶ PR⁻¹Q ⟩)
    where
    lemma :
      Weak-bisimilarity ∞ ⊙ R ⊙ Expansion ∞ ⁻¹ ⊆
      (Expansion ∞ ⊙ R ⁻¹ ⊙ Weak-bisimilarity ∞) ⁻¹
    lemma (_ , P₁≈P₂ , _ , P₂RP₃ , P₃≲P₄) =
      (_ , P₃≲P₄ , _ , P₂RP₃ , symmetric P₁≈P₂)

  -- A variant of 6-5-2-4.

  6-5-2-4′ :
    let Prog = λ (R : Rel₂ ℓ Proc) →
          R ⊆ ⟦ S.StepC ⟧ (Expansion ∞ ⊙ R ⊙ Weak-bisimilarity ∞) in
    ∀ {R} → Prog R → Prog (R ⁻¹) → R ⊆ Weak-bisimilarity ∞
  6-5-2-4′ {R} lr⟶ rl⟶ =
    R                    ⊆⟨ ⊆≈≈ ⟩
    ≈ R ≈                ⊆⟨ unfold _ (λ P≈R≈Q →
                                        StepC.⟨ SS.Step.challenge (lemma lr⟶ P≈R≈Q)
                                              , Σ-map id (Σ-map id ≈≈-sym) ∘
                                                  SS.Step.challenge (lemma rl⟶ (≈≈-sym P≈R≈Q))
                                              ⟩) ⟩∎
    Weak-bisimilarity ∞  ∎
    where
    ≈_≈ : Rel₂ ℓ Proc → Rel₂ ℓ Proc
    ≈ R ≈ = Weak-bisimilarity ∞ ⊙ R ⊙ Weak-bisimilarity ∞

    ⊆≈≈ : ∀ {R} → R ⊆ ≈ R ≈
    ⊆≈≈ r = _ , reflexive , _ , r , reflexive

    ≳_≈ : Rel₂ ℓ Proc → Rel₂ ℓ Proc
    ≳ R ≈ = Expansion ∞ ⊙ R ⊙ Weak-bisimilarity ∞

    ⊆≳≈ : ∀ {R} → R ⊆ ≳ R ≈
    ⊆≳≈ r = _ , reflexive , _ , r , reflexive

    ≈≈-sym : ∀ {R} → ≈ R ≈ ⊆ ≈ R ⁻¹ ≈ ⁻¹
    ≈≈-sym (_ , P₁≈P₂ , _ , P₂RP₃ , P₃≈P₄) =
      (_ , symmetric P₃≈P₄ , _ , P₂RP₃ , symmetric P₁≈P₂)

    lemma : ∀ {R} → R ⊆ ⟦ S.StepC ⟧ ≳ R ≈ → ≈ R ≈ ⊆ SS.Step ≈ R ≈
    lemma {R} lr⟶ = λ where
        (P₁ , P≈P₁ , Q₁ , P₁RQ₁ , Q₁≈Q) .SS.Step.challenge P⟶P₁ →
          let P₁′ , P₁⟶̂P₁′ , P′≈′P₁′ = left-to-right P≈P₁ P⟶P₁
              Q₁′ , Q₁⇒̂Q₁′ , P₁″ ,
                P₁′≳P₁″ , Q₁″ ,
                P₁″RQ₁″ , Q₁″≈Q₁′    = lr≳≈⇒̂ (⊆≳≈ P₁RQ₁) P₁⟶̂P₁′
              Q′ , Q⇒̂Q′  , Q₁′≈Q′    = weak-is-weak⇒̂ Q₁≈Q Q₁⇒̂Q₁′
          in Q′ , Q⇒̂Q′ , P₁″
           , transitive′ {a = ℓ} (force P′≈′P₁′) P₁′≳P₁″
           , Q₁″ , P₁″RQ₁″ , transitive {a = ℓ} Q₁″≈Q₁′ Q₁′≈Q′
      where
      lr⟶̂ :
        ∀ {P P′ Q μ} →
        R (P , Q) → P [ μ ]⟶̂ P′ → ∃ λ Q′ → Q [ μ ]⇒̂ Q′ × ≳ R ≈ (P′ , Q′)
      lr⟶̂ PRQ (done s)    = _ , silent s done , ⊆≳≈ PRQ
      lr⟶̂ PRQ (step P⟶P′) = S.challenge (lr⟶ PRQ) P⟶P′

      lr≳≈⟶ :
        ∀ {P P′ Q μ} →
        ≳ R ≈ (P , Q) → P [ μ ]⟶ P′ →
        ∃ λ Q′ → Q [ μ ]⇒̂ Q′ × ≳ R ≈ (P′ , Q′)
      lr≳≈⟶ (P₁ , P≳P₁ , Q₁ , P₁RQ₁ , Q₁≈Q) P⟶P′ =
        let P₁′ , P₁⟶̂P₁′ , P′≳P₁′          = E.left-to-right P≳P₁ P⟶P′
            Q₁′ , Q₁⇒̂Q₁′ , P₁″ , P₁′≳P₁″ ,
              Q₁″ , P₁″RQ₁″ , Q₁″≈Q₁′      = lr⟶̂ P₁RQ₁ P₁⟶̂P₁′
            Q′ , Q⇒̂Q′ , Q₁′≈Q′             = weak-is-weak⇒̂ Q₁≈Q Q₁⇒̂Q₁′
        in Q′ , Q⇒̂Q′ ,
           P₁″ , transitive {a = ℓ} P′≳P₁′ P₁′≳P₁″ ,
           Q₁″ , P₁″RQ₁″ , transitive {a = ℓ} Q₁″≈Q₁′ Q₁′≈Q′

      lr≳≈⇒ :
        ∀ {P P′ Q} →
        ≳ R ≈ (P , Q) → P ⇒ P′ → ∃ λ Q′ → Q ⇒ Q′ × ≳ R ≈ (P′ , Q′)
      lr≳≈⇒ P≳R≈Q done                = _ , done , P≳R≈Q
      lr≳≈⇒ P≳R≈Q (step s P⟶P′ P′⇒P″) =
        let Q′ , Q⇒̂Q′  , P′≳R≈Q′ = lr≳≈⟶ P≳R≈Q P⟶P′
            Q″ , Q′⇒Q″ , P″≳R≈Q″ = lr≳≈⇒ P′≳R≈Q′ P′⇒P″
        in Q″ , ⇒-transitive (⇒̂→⇒ s Q⇒̂Q′) Q′⇒Q″ , P″≳R≈Q″

      lr≳≈[]⇒ :
        ∀ {P P′ Q μ} →
        ¬ Silent μ →
        ≳ R ≈ (P , Q) → P [ μ ]⇒ P′ →
        ∃ λ Q′ → Q [ μ ]⇒ Q′ × ≳ R ≈ (P′ , Q′)
      lr≳≈[]⇒ ¬s P≳R≈Q (steps P⇒P′ P′⟶P″ P″⇒P‴) =
        let Q′ , Q⇒Q′  , P′≳R≈Q′ = lr≳≈⇒ P≳R≈Q P⇒P′
            Q″ , Q′⇒̂Q″ , P″≳R≈Q″ = lr≳≈⟶ P′≳R≈Q′ P′⟶P″
            Q‴ , Q″⇒Q‴ , P‴≳R≈Q‴ = lr≳≈⇒ P″≳R≈Q″ P″⇒P‴
        in Q‴
         , []⇒⇒-transitive (⇒[]⇒-transitive Q⇒Q′ (⇒̂→[]⇒ ¬s Q′⇒̂Q″)) Q″⇒Q‴
         , P‴≳R≈Q‴

      lr≳≈⇒̂ :
        ∀ {P P′ Q μ} →
        ≳ R ≈ (P , Q) → P [ μ ]⇒̂ P′ →
        ∃ λ Q′ → Q [ μ ]⇒̂ Q′ × ≳ R ≈ (P′ , Q′)
      lr≳≈⇒̂ PRQ = λ where
        (silent s P⇒P′)      → Σ-map id (Σ-map (silent s)      id)
                                 (lr≳≈⇒ PRQ P⇒P′)
        (non-silent ¬s P⇒P′) → Σ-map id (Σ-map (non-silent ¬s) id)
                                 (lr≳≈[]⇒ ¬s PRQ P⇒P′)

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
