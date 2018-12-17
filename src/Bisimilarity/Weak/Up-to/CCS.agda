------------------------------------------------------------------------
-- An up-to technique for CCS
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Bisimilarity.Weak.Up-to.CCS {ℓ} {Name : Set ℓ} where

open import Equality.Propositional
open import Logical-equivalence using (_⇔_)
open import Prelude

open import Function-universe equality-with-J hiding (id; _∘_)

open import Bisimilarity.Weak.CCS
import Bisimilarity.Weak.Equational-reasoning-instances
open import Equational-reasoning
open import Indexed-container hiding (⟨_⟩)
open import Labelled-transition-system.CCS Name
open import Relation

open import Bisimilarity.Weak CCS
open import Bisimilarity.Weak.Up-to CCS
import Labelled-transition-system.Equational-reasoning-instances CCS
  as Dummy

-- Up to (non-degenerate) context for CCS (for polyadic, coinductive
-- contexts).

Up-to-context : Trans₂ ℓ (Proc ∞)
Up-to-context R (p , q) =
  ∃ λ n →
  ∃ λ (C : Context ∞ n) →
  Non-degenerate ∞ C
    ×
  ∃ λ ps →
  ∃ λ qs →
  p ≡ C [ ps ]
    ×
  q ≡ C [ qs ]
    ×
  ∀ x → R (ps x , qs x)

-- Up to context is monotone.

up-to-context-monotone : Monotone Up-to-context
up-to-context-monotone R⊆S =
  Σ-map id $ Σ-map id $ Σ-map id $ Σ-map id $ Σ-map id $ Σ-map id $
  Σ-map id (R⊆S ∘_)

-- Up to context is size-preserving.

up-to-context-size-preserving : Size-preserving Up-to-context
up-to-context-size-preserving =
  _⇔_.from (monotone→⇔ up-to-context-monotone)
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

¬-up-to-context-compatible : Name → ¬ Compatible Up-to-context
¬-up-to-context-compatible x comp = contradiction
  where
  a = x , true

  data R₀ : Rel₂ ℓ (Proc ∞) where
    base : R₀ (τ ∙ (a ∙) , a ∙)

  R : Rel₂ ℓ (Proc ∞)
  R = R₀ ⁼

  !τa[R]!a : Up-to-context R (! τ ∙ (a ∙) , ! a ∙)
  !τa[R]!a =
      1
    , ! hole fzero
    , ! hole
    , (λ _ → τ ∙ (a ∙))
    , (λ _ → a ∙)
    , refl
    , refl
    , (λ _ → inj₁ base)

  !a[τ]⇒̂→≡ : ∀ {P} → ! a ∙ [ τ ]⇒̂ P → P ≡ ! a ∙
  !a[τ]⇒̂→≡ (non-silent ¬s _)                 = ⊥-elim $ ¬s _
  !a[τ]⇒̂→≡ (silent _ done)                   = refl
  !a[τ]⇒̂→≡ (silent _ (step {μ = μ} s !a⟶ _)) = ⊥-elim $ name≢τ (
                                                 name a  ≡⟨ !-only ·-only !a⟶ ⟩
                                                 μ       ≡⟨ silent≡τ s ⟩∎
                                                 τ       ∎)

  drop-[] : ∀ {P Q S} →
            Up-to-context R (P ∣ Q , ! S) → R (P ∣ Q , ! S)
  drop-[] (_ , hole i , _ , _ , _ , P∣Q≡Ps[i] , !S≡Qs[i] , PsRQs) =
    subst R (cong₂ _,_ (sym P∣Q≡Ps[i]) (sym !S≡Qs[i])) (PsRQs i)

  drop-[] (_ , ∅        , _ , _ , _ , () , _)
  drop-[] (_ , _ ∣ _    , _ , _ , _ , _  , () , _)
  drop-[] (_ , _ ⊕ _    , _ , _ , _ , () , _)
  drop-[] (_ , _ · _    , _ , _ , _ , () , _)
  drop-[] (_ , ⟨ν _ ⟩ _ , _ , _ , _ , () , _)
  drop-[] (_ , ! _      , _ , _ , _ , () , _)

  R⊆StepR : R ⊆ ⟦ StepC ⟧ R
  R⊆StepR (inj₁ base) = ⟨ lr , rl ⟩
    where
    lr :
      ∀ {P μ} →
      τ ∙ (a ∙) [ μ ]⟶ P →
      ∃ λ Q → a ∙ [ μ ]⇒̂ Q × R (P , Q)
    lr action =
        _
      , (a ∙  ■)
      , inj₂ refl

    rl :
      ∀ {Q μ} →
      a ∙ [ μ ]⟶ Q →
      ∃ λ P → τ ∙ (a ∙) [ μ ]⇒̂ P × R (P , Q)
    rl action =
        _
      , (τ ∙ (a ∙)  →⟨ ⟶: action ⟩
         a ∙        →⟨ ⟶: action ⟩■
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

  [R]⊆Step[R] : Up-to-context R ⊆ ⟦ StepC ⟧ (Up-to-context R)
  [R]⊆Step[R] =
    Up-to-context R              ⊆⟨ up-to-context-monotone (λ {x} → R⊆StepR {x}) ⟩
    Up-to-context (⟦ StepC ⟧ R)  ⊆⟨ comp ⟩∎
    ⟦ StepC ⟧ (Up-to-context R)  ∎

  contradiction : ⊥
  contradiction =                                                       $⟨ !τa[R]!a ⟩
    Up-to-context R (! τ ∙ (a ∙) , ! a ∙)                               ↝⟨ [R]⊆Step[R] ⟩
    ⟦ StepC ⟧ (Up-to-context R) (! τ ∙ (a ∙) , ! a ∙)                   ↝⟨ (λ s → StepC.left-to-right s (replication (par-right action))) ⟩
    (∃ λ P → ! a ∙ [ τ ]⇒̂ P × Up-to-context R (! τ ∙ (a ∙) ∣ a ∙ , P))  ↝⟨ (λ { (_ , !a⟶ , hyp) →
                                                                                  subst (Up-to-context R ∘ (_ ,_)) (!a[τ]⇒̂→≡ !a⟶) hyp }) ⟩
    Up-to-context R (! τ ∙ (a ∙) ∣ a ∙ , ! a ∙)                         ↝⟨ drop-[] ⟩
    R (! τ ∙ (a ∙) ∣ a ∙ , ! a ∙)                                       ↝⟨ [ (λ ()) , (λ ()) ] ⟩□
    ⊥                                                                   □
