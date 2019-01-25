------------------------------------------------------------------------
-- Some results related to an LTS from Section 6.2.5 of "Enhancements
-- of the bisimulation proof method" by Pous and Sangiorgi,
-- implemented using the coinductive definition of bisimilarity
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe --sized-types #-}

module Bisimilarity.6-2-5 {Name : Set} where

open import Equality.Propositional
open import Logical-equivalence using (_⇔_)
open import Prelude
open import Size

open import Function-universe equality-with-J hiding (id; _∘_)

import Bisimilarity.Equational-reasoning-instances
open import Equational-reasoning
open import Indexed-container using (⟦_⟧)
open import Labelled-transition-system.6-2-5 Name
open import Relation

open import Bisimilarity 6-2-5
open import Bisimilarity.Up-to 6-2-5

-- Some simple lemmas. The first two are stated by Pous and Sangiorgi,
-- and the third one is a generalisation of a result stated by Pous
-- and Sangiorgi.

op·∅ : ∀ {a} → op (a · ∅) ∼ ∅
op·∅ {a} = ⟨ lr , (λ ()) ⟩
  where
  lr : ∀ {P′ μ} →
       op (a · ∅) [ μ ]⟶ P′ →
       ∃ λ Q′ → ∅ [ μ ]⟶ Q′ × P′ ∼′ Q′
  lr (op action ())

op··∅ : ∀ {a} → op (a · a · ∅) ∼ a · ∅
op··∅ {a} = ⟨ lr , rl ⟩
  where
  lr : ∀ {P′ μ b} →
       op (a · b · ∅) [ μ ]⟶ P′ →
       ∃ λ Q′ → b · ∅ [ μ ]⟶ Q′ × P′ ∼′ Q′
  lr (op action action) = _ , action , reflexive

  rl : ∀ {Q′ μ} →
       a · ∅ [ μ ]⟶ Q′ →
       ∃ λ P′ → op (a · a · ∅) [ μ ]⟶ P′ × P′ ∼′ Q′
  rl action = _ , op action action , reflexive

a≁b·c : ∀ {a b c} → ¬ (a · ∅ ∼ b · c · ∅)
a≁b·c a∼b·c with right-to-left a∼b·c action
... | .∅ , action , ∅∼a with right-to-left (force ∅∼a) action
...   | _ , () , _

-- Pous and Sangiorgi note that every context preserves bisimilarity.
-- One can prove that a ·_ preserves bisimilarity in a size-preserving
-- way.

·-cong : ∀ {i a P Q} → [ i ] P ∼ Q → [ i ] a · P ∼ a · Q
·-cong {i} {a} P∼Q =
  ⟨ lr P∼Q
  , Σ-map id (Σ-map id symmetric) ∘ lr (symmetric P∼Q)
  ⟩
  where
  lr : ∀ {P P′ Q μ} →
       [ i ] P ∼ Q → a · P [ μ ]⟶ P′ →
       ∃ λ Q′ → a · Q [ μ ]⟶ Q′ × [ i ] P′ ∼′ Q′
  lr P∼Q action = _ , action , convert P∼Q

-- The operator op also preserves bisimilarity, but this lemma is not
-- claimed to be size-preserving.

op-cong : ∀ {i} {j : Size< i} {P Q} →
          [ i ] P ∼ Q → [ j ] op P ∼ op Q
op-cong {i} {j} P∼Q =
  ⟨ lr P∼Q
  , Σ-map id (Σ-map id symmetric) ∘ lr (symmetric P∼Q)
  ⟩
  where
  lr : ∀ {P P′ Q μ} →
       [ i ] P ∼ Q → op P [ μ ]⟶ P′ →
       ∃ λ Q′ → op Q [ μ ]⟶ Q′ × [ j ] P′ ∼′ Q′
  lr P∼Q (op P⟶P′ P′⟶P″) =
    let Q′ , Q⟶Q′  , P′∼Q′ = left-to-right        P∼Q    P⟶P′
        Q″ , Q′⟶Q″ , P″∼Q″ = left-to-right (force P′∼Q′) P′⟶P″
    in Q″ , op Q⟶Q′ Q′⟶Q″ , P″∼Q″

-- Let us assume that the Name type is inhabited. In that case op-cong
-- /cannot/ preserve the size of its argument.
--
-- The proof is based on an argument presented by Pous and Sangiorgi.

op-cong-cannot-preserve-size :
  Name →
  ¬ (∀ {i P Q} → [ i ] P ∼ Q → [ i ] op P ∼ op Q)
op-cong-cannot-preserve-size a op-cong = a≁b·c a∼a·a
  where
  op-cong′ : ∀ {i P Q} → [ i ] P ∼′ Q → [ i ] op P ∼′ op Q
  force (op-cong′ P∼′Q) = op-cong (force P∼′Q)

  a∼a·a : ∀ {i} → [ i ] a · ∅ ∼ a · a · ∅
  a∼a·a {i} = ⟨ lr , rl ⟩
    where
    a∼′a·a : ∀ {i} → [ i ] a · ∅ ∼′ a · a · ∅
    force a∼′a·a = a∼a·a

    lemma =
      ∅               ∼⟨ symmetric op·∅ ⟩
      op (a · ∅)      ∼⟨ op-cong′ (a∼′a·a {i = i}) ⟩
      op (a · a · ∅)  ∼⟨ op··∅ ⟩■
      a · ∅

    lr : ∀ {P′ μ} →
         a · ∅ [ μ ]⟶ P′ →
         ∃ λ Q′ → a · a · ∅ [ μ ]⟶ Q′ × [ i ] P′ ∼′ Q′
    lr action = a · ∅ , action , lemma

    rl : ∀ {Q′ μ} →
         a · a · ∅ [ μ ]⟶ Q′ →
         ∃ λ P′ → a · ∅ [ μ ]⟶ P′ × [ i ] P′ ∼′ Q′
    rl action = ∅ , action , lemma

-- Up to context (for monadic contexts).

Up-to-context : Trans₂ (# 0) Proc
Up-to-context R (P , Q) =
  ∃ λ (C : Context 1) →
  ∃ λ P′ →
  ∃ λ Q′ →
  P ≡ C [ (λ _ → P′) ]
    ×
  Q ≡ C [ (λ _ → Q′) ]
    ×
  R (P′ , Q′)

-- Up to context is monotone.

up-to-context-monotone : Monotone Up-to-context
up-to-context-monotone R⊆S =
  Σ-map id $ Σ-map id $ Σ-map id $ Σ-map id $ Σ-map id R⊆S

-- Up to bisimilarity and context.

Up-to-bisimilarity-and-context : Trans₂ (# 0) Proc
Up-to-bisimilarity-and-context =
  Up-to-bisimilarity ∘ Up-to-context

-- Up to bisimilarity and context is monotone.

up-to-bisimilarity-and-context-monotone :
  Monotone Up-to-bisimilarity-and-context
up-to-bisimilarity-and-context-monotone =
  up-to-bisimilarity-monotone ∘ up-to-context-monotone

-- Up to bisimilarity and context is not sound (assuming that Name is
-- inhabited).
--
-- This result is due to Pous and Sangiorgi.

¬-up-to-bisimilarity-and-context :
  Name →
  ¬ Up-to-technique Up-to-bisimilarity-and-context
¬-up-to-bisimilarity-and-context a =
  Up-to-technique Up-to-bisimilarity-and-context  ↝⟨ _$ R⊆ ⟩
  R ⊆ Bisimilarity ∞                              ↝⟨ R⊈∼ ⟩□
  ⊥                                               □
  where
  data R : Rel₂ (# 0) Proc where
    base : R (a · ∅ , a · a · ∅)

  lemma : Up-to-bisimilarity-and-context R (∅ , a · ∅)
  lemma =
    op (a · ∅) ,
    symmetric op·∅ ,
    op (a · a · ∅) ,
    (op (hole fzero) , a · ∅ , a · a · ∅ , refl , refl , base) ,
    op··∅

  R⊆ : R ⊆ ⟦ StepC ⟧ (Up-to-bisimilarity-and-context R)
  R⊆ base =
    ⟨ (λ { action → a · ∅ , action , lemma })
    , (λ { action → ∅     , action , lemma })
    ⟩

  R⊈∼ : ¬ R ⊆ Bisimilarity ∞
  R⊈∼ =
    R ⊆ Bisimilarity ∞  ↝⟨ (λ R⊆∼ → R⊆∼ base) ⟩
    a · ∅ ∼ a · a · ∅   ↝⟨ a≁b·c ⟩□
    ⊥                   □

-- The last result above can be used to give another proof showing
-- that op-cong cannot preserve the size of its argument (assuming
-- that Name is inhabited).

op-cong-cannot-preserve-size′ :
  Name →
  ¬ (∀ {i P Q} → [ i ] P ∼ Q → [ i ] op P ∼ op Q)
op-cong-cannot-preserve-size′ a =
  (∀ {i P Q} → [ i ] P ∼ Q → [ i ] op P ∼ op Q)               ↝⟨ (λ op-cong C P∼Q → []-cong op-cong C (λ _ → P∼Q)) ⟩

  (∀ {i P Q} (C : Context 1) → [ i ] P ∼ Q →
   [ i ] C [ (λ _ → P) ] ∼ C [ (λ _ → Q) ])                   ↝⟨ (λ []-cong → λ where
                                                                    {x = P , Q} (_ , P∼C[R₁] , _ ,
                                                                                 (C , R₁ , R₂ , refl , refl , R₁∼R₂) , C[R₂]∼Q) →

                                                                      P                 ∼⟨ P∼C[R₁] ⟩
                                                                      C [ (λ _ → R₁) ]  ∼⟨ []-cong C R₁∼R₂ ⟩
                                                                      C [ (λ _ → R₂) ]  ∼⟨ C[R₂]∼Q ⟩■
                                                                      Q) ⟩
  (∀ {i} → Up-to-bisimilarity-and-context (Bisimilarity i) ⊆
           Bisimilarity i)                                    ↝⟨ _⇔_.from (monotone→⇔ up-to-bisimilarity-and-context-monotone) ⟩

  Size-preserving Up-to-bisimilarity-and-context              ↝⟨ size-preserving→up-to ⟩

  Up-to-technique Up-to-bisimilarity-and-context              ↝⟨ ¬-up-to-bisimilarity-and-context a ⟩□

  ⊥                                                           □
  where
  []-cong :
    (∀ {i P Q} → [ i ] P ∼ Q → [ i ] op P ∼ op Q) →
    ∀ {i n Ps Qs}
    (C : Context n) → (∀ x → [ i ] Ps x ∼ Qs x) →
    [ i ] C [ Ps ] ∼ C [ Qs ]
  []-cong op-cong (hole x) Ps∼Qs = Ps∼Qs x
  []-cong op-cong (op C)   Ps∼Qs = op-cong ([]-cong op-cong C Ps∼Qs)
  []-cong op-cong (a · C)  Ps∼Qs = ·-cong ([]-cong op-cong C Ps∼Qs)
  []-cong op-cong ∅        Ps∼Qs = reflexive
