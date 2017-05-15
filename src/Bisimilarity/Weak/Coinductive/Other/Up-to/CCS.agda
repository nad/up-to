------------------------------------------------------------------------
-- An up-to technique for CCS
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

open import Labelled-transition-system

module Bisimilarity.Weak.Coinductive.Other.Up-to.CCS {Name : Set} where

open import Equality.Propositional
open import Logical-equivalence using (_⇔_)
open import Prelude

open import Function-universe equality-with-J hiding (id; _∘_)

open CCS Name
open LTS CCS hiding (Proc; _[_]⟶_)

open import Bisimilarity.Weak.CCS
open import Bisimilarity.Weak.Coinductive.Other CCS
import
  Bisimilarity.Weak.Coinductive.Other.Equational-reasoning-instances
open import Bisimilarity.Weak.Coinductive.Other.Up-to CCS
open import Equational-reasoning
open import Indexed-container hiding (⟨_⟩)
import Labelled-transition-system.Equational-reasoning-instances CCS
  as Unused
open import Relation

-- Up to (non-degenerate) context for CCS (for polyadic contexts).

Up-to-context : Trans₂ (# 0) Proc
Up-to-context R (p , q) =
  ∃ λ n →
  ∃ λ (C : Context n) →
  Non-degenerate C
    ×
  ∃ λ ps →
  ∃ λ qs →
  p ≡ C [ ps ]
    ×
  q ≡ C [ qs ]
    ×
  ∀ x → R (ps x , qs x)

-- Up to context is monotone.

Up-to-context-monotone : Monotone Up-to-context
Up-to-context-monotone R⊆S =
  Σ-map id $ Σ-map id $ Σ-map id $ Σ-map id $ Σ-map id $ Σ-map id $
  Σ-map id (R⊆S ∘_)

-- Up to context is size-preserving.

Up-to-context-size-preserving : Size-preserving Up-to-context
Up-to-context-size-preserving =
  _⇔_.from (monotone→⇔ Up-to-context-monotone)
  (λ where
     (_ , C , D , ps , qs , refl , refl , ps∼qs) →

      C [ ps ]  ∼⟨ D [ ps∼qs ]-cong ⟩■
      C [ qs ])

-- Note that up to context is not compatible (assuming that Name is
-- inhabited).
--
-- This counterexample is a minor variant of one due to Pous and
-- Sangiorgi, who state that up to context is contained in a larger
-- function that is compatible for another, "one-sided" step function
-- (see Section 6.5.3 in "Enhancements of the bisimulation proof
-- method").

¬-Up-to-context-compatible : Name → ¬ Compatible Up-to-context
¬-Up-to-context-compatible x comp = contradiction
  where
  a = x , true

  data R₀ : Rel₂ (# 0) Proc where
    base : R₀ (τ · (a ·) , a ·)

  R : Rel₂ (# 0) Proc
  R = R₀ ⁼

  !τa[R]!a : Up-to-context R (! τ · (a ·) , ! a ·)
  !τa[R]!a =
      1
    , ! hole fzero
    , ! hole
    , (λ _ → τ · (a ·))
    , (λ _ → a ·)
    , refl
    , refl
    , (λ _ → inj₁ base)

  !a[τ]⇒̂→≡ : ∀ {P} → ! a · [ τ ]⇒̂ P → P ≡ ! a ·
  !a[τ]⇒̂→≡ (silent refl done)              = refl
  !a[τ]⇒̂→≡ (silent refl (step refl !a⟶ _)) = ⊥-elim $ name≢τ $
                                               !-only ·-only !a⟶
  !a[τ]⇒̂→≡ (non-silent ¬s _)               = ⊥-elim $ ¬s refl

  drop-[] : ∀ {P Q S} →
            Up-to-context R (P ∣ Q , ! S) → R (P ∣ Q , ! S)
  drop-[] (_ , hole i , _ , _ , _ , P∣Q≡Ps[i] , !S≡Qs[i] , PsRQs) =
    subst R (cong₂ _,_ (sym P∣Q≡Ps[i]) (sym !S≡Qs[i])) (PsRQs i)

  drop-[] (_ , ∅     , _ , _ , _ , () , _)
  drop-[] (_ , _ ∣ _ , _ , _ , _ , _  , () , _)
  drop-[] (_ , _ ⊕ _ , _ , _ , _ , () , _)
  drop-[] (_ , _ · _ , _ , _ , _ , () , _)
  drop-[] (_ , ν _ _ , _ , _ , _ , () , _)
  drop-[] (_ , ! _   , _ , _ , _ , () , _)

  R⊆StepR : R ⊆ ⟦ S̲t̲e̲p̲ ⟧ R
  R⊆StepR (inj₁ base) = ⟨ lr , rl ⟩
    where
    lr :
      ∀ {P μ} →
      τ · (a ·) [ μ ]⟶ P →
      ∃ λ Q → a · [ μ ]⇒̂ Q × R (P , Q)
    lr action =
        _
      , (a ·  ■)
      , inj₂ refl

    rl :
      ∀ {Q μ} →
      a · [ μ ]⟶ Q →
      ∃ λ P → τ · (a ·) [ μ ]⇒̂ P × R (P , Q)
    rl action =
        _
      , (τ · (a ·)  →⟨ ⟶: action ⟩
         a ·        →⟨ ⟶: action ⟩■
         ∅)
      , inj₂ refl

  R⊆StepR {P , _} (inj₂ refl) =
    ⟨ Σ-map id (Σ-map id inj₂)         ∘ lr
    , Σ-map id (Σ-map id (inj₂ ∘ sym)) ∘ lr
    ⟩
    where
    lr : ∀ {P′ μ} →
         P [ μ ]⟶ P′ →
         ∃ λ Q′ → P [ μ ]⇒̂ Q′ × P′ ≡ Q′
    lr P⟶P′ = _ , ⟶→⇒̂ P⟶P′ , refl

  -- Note the use of compatibility in [R]⊆Step[S].

  [R]⊆Step[R] : Up-to-context R ⊆ ⟦ S̲t̲e̲p̲ ⟧ (Up-to-context R)
  [R]⊆Step[R] =
    Up-to-context R             ⊆⟨ Up-to-context-monotone (λ {x} → R⊆StepR {x}) ⟩
    Up-to-context (⟦ S̲t̲e̲p̲ ⟧ R)  ⊆⟨ comp _ ⟩∎
    ⟦ S̲t̲e̲p̲ ⟧ (Up-to-context R)  ∎

  contradiction : ⊥
  contradiction =                                                       $⟨ !τa[R]!a ⟩
    Up-to-context R (! τ · (a ·) , ! a ·)                               ↝⟨ [R]⊆Step[R] ⟩
    ⟦ S̲t̲e̲p̲ ⟧ (Up-to-context R) (! τ · (a ·) , ! a ·)                    ↝⟨ (λ s → S̲t̲e̲p̲.left-to-right s (replication (par-right action))) ⟩
    (∃ λ P → ! a · [ τ ]⇒̂ P × Up-to-context R (! τ · (a ·) ∣ a · , P))  ↝⟨ (λ { (_ , !a⟶ , hyp) →
                                                                                  subst (Up-to-context R ∘ (_ ,_)) (!a[τ]⇒̂→≡ !a⟶) hyp }) ⟩
    Up-to-context R (! τ · (a ·) ∣ a · , ! a ·)                         ↝⟨ drop-[] ⟩
    R (! τ · (a ·) ∣ a · , ! a ·)                                       ↝⟨ [ (λ ()) , (λ ()) ] ⟩□
    ⊥                                                                   □
