------------------------------------------------------------------------
-- Lemmas related to strong similarity for CCS
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe --sized-types #-}

module Similarity.CCS {ℓ} {Name : Set ℓ} where

open import Equality.Propositional
open import Prelude
open import Size

open import Function-universe equality-with-J hiding (id; _∘_)

import Bisimilarity.CCS as BL
import Bisimilarity.Equational-reasoning-instances
open import Equational-reasoning
open import Labelled-transition-system.CCS Name
import Similarity.Equational-reasoning-instances

open import Bisimilarity CCS as B using (_∼_; _∼′_)
open import Similarity CCS

------------------------------------------------------------------------
-- Congruence lemmas

private
  module CL {i} = BL.Cong-lemmas [ i ]_≤′_ challenge

mutual

  -- _∣_ preserves similarity.

  infix 6 _∣-cong_ _∣-cong′_

  _∣-cong_ : ∀ {i P P′ Q Q′} →
             [ i ] P ≤ P′ → [ i ] Q ≤ Q′ → [ i ] P ∣ Q ≤ P′ ∣ Q′
  P≤P′ ∣-cong Q≤Q′ = ⟨ CL.∣-cong _∣-cong′_ P≤P′ Q≤Q′ ⟩

  _∣-cong′_ : ∀ {i P P′ Q Q′} →
              [ i ] P ≤′ P′ → [ i ] Q ≤′ Q′ → [ i ] P ∣ Q ≤′ P′ ∣ Q′
  force (P≤P′ ∣-cong′ Q≤Q′) = force P≤P′ ∣-cong force Q≤Q′

-- _⊕_ preserves similarity.

infix 8 _⊕-cong_ _⊕-cong′_

_⊕-cong_ : ∀ {i P P′ Q Q′} →
           [ i ] P ≤ P′ → [ i ] Q ≤ Q′ → [ i ] P ⊕ Q ≤ P′ ⊕ Q′
P≤P′ ⊕-cong Q≤Q′ = ⟨ CL.⊕-cong P≤P′ Q≤Q′ ⟩

_⊕-cong′_ : ∀ {i P P′ Q Q′} →
            [ i ] P ≤′ P′ → [ i ] Q ≤′ Q′ → [ i ] P ⊕ Q ≤′ P′ ⊕ Q′
force (P≤P′ ⊕-cong′ Q≤Q′) = force P≤P′ ⊕-cong force Q≤Q′

-- _·_ preserves similarity.

infix 12 _·-cong_ _·-cong′_

_·-cong_ :
  ∀ {i μ μ′ P P′} →
  μ ≡ μ′ → [ i ] force P ≤′ force P′ → [ i ] μ · P ≤ μ′ · P′
_·-cong_ {i} refl P≤P′ = ⟨ CL.·-cong {i = i} P≤P′ ⟩

_·-cong′_ :
  ∀ {i μ μ′ P P′} →
  μ ≡ μ′ → [ i ] force P ≤′ force P′ → [ i ] μ · P ≤′ μ′ · P′
force (μ≡μ′ ·-cong′ P≤P′) = μ≡μ′ ·-cong P≤P′

-- _∙_ preserves similarity.

infix 12 _∙-cong_ _∙-cong′_

_∙-cong_ : ∀ {i μ μ′ P P′} →
           μ ≡ μ′ → [ i ] P ≤ P′ → [ i ] μ ∙ P ≤ μ′ ∙ P′
refl ∙-cong P≤P′ = refl ·-cong convert {a = ℓ} P≤P′

_∙-cong′_ : ∀ {i μ μ′ P P′} →
            μ ≡ μ′ → [ i ] P ≤′ P′ → [ i ] μ ∙ P ≤′ μ′ ∙ P′
force (μ≡μ′ ∙-cong′ P≤P′) = μ≡μ′ ∙-cong force P≤P′

-- _∙ turns equal actions into similar processes.

infix 12 _∙-cong _∙-cong′

_∙-cong : ∀ {μ μ′} → μ ≡ μ′ → μ ∙ ≤ μ′ ∙
refl ∙-cong = reflexive

_∙-cong′ : ∀ {μ μ′} → μ ≡ μ′ → μ ∙ ≤′ μ′ ∙
refl ∙-cong′ = reflexive

mutual

  -- ⟨ν_⟩ preserves similarity.

  ⟨ν_⟩-cong : ∀ {i a a′ P P′} →
              a ≡ a′ → [ i ] P ≤ P′ → [ i ] ⟨ν a ⟩ P ≤ ⟨ν a′ ⟩ P′
  ⟨ν refl ⟩-cong P≤P′ = ⟨ CL.⟨ν⟩-cong ⟨ν refl ⟩-cong′ P≤P′ ⟩

  ⟨ν_⟩-cong′ : ∀ {i a a′ P P′} →
               a ≡ a′ → [ i ] P ≤′ P′ → [ i ] ⟨ν a ⟩ P ≤′ ⟨ν a′ ⟩ P′
  force (⟨ν a≡a′ ⟩-cong′ P≤P′) = ⟨ν a≡a′ ⟩-cong (force P≤P′)

mutual

  -- !_ preserves similarity.

  infix 10 !-cong_ !-cong′_

  !-cong_ : ∀ {i P P′} →
            [ i ] P ≤ P′ → [ i ] ! P ≤ ! P′
  !-cong P≤P′ = ⟨ CL.!-cong BL.6-1-3-2 _∣-cong′_ !-cong′_ P≤P′ ⟩

  !-cong′_ : ∀ {i P P′} → [ i ] P ≤′ P′ → [ i ] ! P ≤′ ! P′
  force (!-cong′ P≤P′) = !-cong force P≤P′

-- _[_] preserves similarity.

mutual

  infix 5 _[_]-cong _[_]-cong′

  _[_]-cong :
    ∀ {i n Ps Qs}
    (C : Context ∞ n) → (∀ x → [ i ] Ps x ≤ Qs x) →
    [ i ] C [ Ps ] ≤ C [ Qs ]
  hole x   [ Ps≤Qs ]-cong = Ps≤Qs x
  ∅        [ Ps≤Qs ]-cong = reflexive
  C₁ ∣ C₂  [ Ps≤Qs ]-cong = (C₁ [ Ps≤Qs ]-cong) ∣-cong (C₂ [ Ps≤Qs ]-cong)
  C₁ ⊕ C₂  [ Ps≤Qs ]-cong = (C₁ [ Ps≤Qs ]-cong) ⊕-cong (C₂ [ Ps≤Qs ]-cong)
  μ · C    [ Ps≤Qs ]-cong = refl ·-cong λ { .force → force C [ Ps≤Qs ]-cong }
  ⟨ν a ⟩ C [ Ps≤Qs ]-cong = ⟨ν refl ⟩-cong (C [ Ps≤Qs ]-cong)
  ! C      [ Ps≤Qs ]-cong = !-cong (C [ Ps≤Qs ]-cong)

  _[_]-cong′ :
    ∀ {i n Ps Qs}
    (C : Context ∞ n) → (∀ x → [ i ] Ps x ≤′ Qs x) →
    [ i ] C [ Ps ] ≤′ C [ Qs ]
  force (C [ Ps≤Qs ]-cong′) = C [ (λ x → force (Ps≤Qs x)) ]-cong

------------------------------------------------------------------------
-- Other results

-- P is similar to P ⊕ Q.

≤-⊕-left : ∀ {i P Q} → [ i ] P ≤ P ⊕ Q
≤-⊕-left = ⟨ (λ P⟶P′ → _ , sum-left P⟶P′ , reflexive) ⟩

-- Q is similar to P ⊕ Q.

≤-⊕-right : ∀ {i P Q} → [ i ] Q ≤ P ⊕ Q
≤-⊕-right = ⟨ (λ Q⟶Q′ → _ , sum-right Q⟶Q′ , reflexive) ⟩

-- If Name is inhabited, then there are two processes that are similar
-- in both directions, but not bisimilar.
--
-- I took this example from Wikipedia; I suspect that it is due to
-- Milner.

≤≥≁ : Name → ∃ λ P → ∃ λ Q → P ≤ Q × Q ≤ P × ¬ P ∼ Q
≤≥≁ x = machine₁ , machine₂
      , machine₁≤machine₂ , machine₂≤machine₁ , machine₁≁machine₂
  where

  -- Some names (with kinds), constructed using x.

  pay coffee tea : Name-with-kind

  pay    = x , true
  coffee = pay
  tea    = x , false

  -- Two vending machines.

  machine₁ machine₂ machine₁′ machine₂′ : Proc ∞

  machine₁′ = name pay ∙ (coffee ∙ ⊕ tea ∙)
  machine₁  = ! machine₁′

  machine₂′ = (name pay ∙ (coffee ∙) ⊕ name pay ∙ (tea ∙))
                ⊕
              machine₁′
  machine₂  = ! machine₂′

  -- A lemma.

  machine₁⟶ :
    ∀ {P μ} → machine₁ [ μ ]⟶ P →
    μ ≡ name pay × P ∼ machine₁ ∣ (coffee ∙ ⊕ tea ∙)
  machine₁⟶ tr = case BL.6-1-3-2 tr of λ where
    (inj₁ (_ , action , P∼))                 → refl , P∼
    (inj₂ (_ , _ , _ , _ , action , tr , _)) →
      ⊥-elim (names-are-not-inverted tr)

  -- The first machine is similar to the second one.

  machine₁≤machine₂ : ∀ {i} → [ i ] machine₁ ≤ machine₂
  machine₁≤machine₂ {i} =
    StepC.⟨ (λ {P} tr →
               case machine₁⟶ tr of λ where
                 (refl , P∼) →
                     _
                   , (machine₂                      [ name pay ]⟶⟨ replication (par-right (sum-right action)) ⟩
                      machine₂ ∣ coffee ∙ ⊕ tea ∙)
                   , (P                            ∼⟨ ≤: convert {a = ℓ} P∼ ⟩
                      machine₁ ∣ coffee ∙ ⊕ tea ∙  ∼⟨ machine₁≤′machine₂ ∣-cong′ (_ ■) ⟩■
                      machine₂ ∣ coffee ∙ ⊕ tea ∙))
          ⟩
    where
    machine₁≤′machine₂ : [ i ] machine₁ ≤′ machine₂
    force machine₁≤′machine₂ = machine₁≤machine₂

  -- The second machine is similar to the first one.

  machine₂≤machine₁ : ∀ {i} → [ i ] machine₂ ≤ machine₁
  machine₂≤machine₁ {i} = StepC.⟨ helper ∘ BL.6-1-3-2 ⟩
    where
    machine₂≤′machine₁ : [ i ] machine₂ ≤′ machine₁
    force machine₂≤′machine₁ = machine₂≤machine₁

    lemma =
      machine₁                     [ name pay ]⟶⟨ replication (par-right action) ⟩
      machine₁ ∣ coffee ∙ ⊕ tea ∙

    helper :
      ∀ {P μ} →
      (∃ λ P′ → machine₂′ [ μ ]⟶ P′ × P ∼ machine₂ ∣ P′)
        ⊎
      (μ ≡ τ × ∃ λ P′ → ∃ λ P″ → ∃ λ a →
       machine₂′ [ name a ]⟶ P′ × machine₂′ [ name (co a) ]⟶ P″ ×
       P ∼ (machine₂ ∣ P′) ∣ P″) →
      ∃ λ Q → machine₁ [ μ ]⟶ Q × [ i ] P ≤′ Q
    helper {P} (inj₁ (_ , sum-left (sum-left action) , P∼)) =
        _
      , lemma
      , (P                            ∼⟨ ≤: convert {a = ℓ} P∼ ⟩
         machine₂ ∣ coffee ∙          ∼⟨ machine₂≤′machine₁ ∣-cong′ convert {a = ℓ} ≤-⊕-left ⟩■
         machine₁ ∣ coffee ∙ ⊕ tea ∙)

    helper {P} (inj₁ (_ , sum-left (sum-right action) , P∼)) =
        _
      , lemma
      , (P                            ∼⟨ ≤: convert {a = ℓ} P∼ ⟩
         machine₂ ∣ tea ∙             ∼⟨ machine₂≤′machine₁ ∣-cong′ convert {a = ℓ} ≤-⊕-right ⟩■
         machine₁ ∣ coffee ∙ ⊕ tea ∙)

    helper {P} (inj₁ (_ , sum-right action , P∼)) =
        _
      , lemma
      , (P                            ∼⟨ ≤: convert {a = ℓ} P∼ ⟩
         machine₂ ∣ coffee ∙ ⊕ tea ∙  ∼⟨ machine₂≤′machine₁ ∣-cong′ (_ ■) ⟩■
         machine₁ ∣ coffee ∙ ⊕ tea ∙)

    helper (inj₂ (_ , _ , _ , _ , sum-left (sum-left action)  , sum-left (sum-left tr)  , _)) = ⊥-elim (names-are-not-inverted tr)
    helper (inj₂ (_ , _ , _ , _ , sum-left (sum-left action)  , sum-left (sum-right tr) , _)) = ⊥-elim (names-are-not-inverted tr)
    helper (inj₂ (_ , _ , _ , _ , sum-left (sum-left action)  , sum-right tr            , _)) = ⊥-elim (names-are-not-inverted tr)
    helper (inj₂ (_ , _ , _ , _ , sum-left (sum-right action) , sum-left (sum-left tr)  , _)) = ⊥-elim (names-are-not-inverted tr)
    helper (inj₂ (_ , _ , _ , _ , sum-left (sum-right action) , sum-left (sum-right tr) , _)) = ⊥-elim (names-are-not-inverted tr)
    helper (inj₂ (_ , _ , _ , _ , sum-left (sum-right action) , sum-right tr            , _)) = ⊥-elim (names-are-not-inverted tr)
    helper (inj₂ (_ , _ , _ , _ , sum-right action            , sum-left (sum-left tr)  , _)) = ⊥-elim (names-are-not-inverted tr)
    helper (inj₂ (_ , _ , _ , _ , sum-right action            , sum-left (sum-right tr) , _)) = ⊥-elim (names-are-not-inverted tr)
    helper (inj₂ (_ , _ , _ , _ , sum-right action            , sum-right tr            , _)) = ⊥-elim (names-are-not-inverted tr)

  -- The two machines are not bisimilar.

  machine₁≁machine₂ : ¬ machine₁ ∼ machine₂
  machine₁≁machine₂ =
    machine₁ ∼ machine₂                                            ↝⟨ (λ hyp → B.right-to-left hyp
                                                                                 (replication (par-right (sum-left (sum-left action))))) ⟩

    (∃ λ P → machine₁ [ name pay ]⟶ P × P ∼′ machine₂ ∣ coffee ∙)  ↝⟨ Σ-map id (Σ-map (proj₂ ∘ machine₁⟶) id) ⟩

    (∃ λ P → P ∼ machine₁ ∣ (coffee ∙ ⊕ tea ∙) ×
             P ∼′ machine₂ ∣ coffee ∙)                             ↝⟨ (λ { (_ , P∼ , P∼′) → transitive {a = ℓ} (symmetric P∼) (convert {a = ℓ} P∼′) }) ⟩

    machine₁ ∣ (coffee ∙ ⊕ tea ∙) ∼ machine₂ ∣ coffee ∙            ↝⟨ (λ hyp → Σ-map id proj₁ $
                                                                                 B.left-to-right hyp (par-right (sum-right action))) ⟩

    (∃ λ P → machine₂ ∣ coffee ∙ [ name tea ]⟶ P)                  ↝⟨ helper ∘ proj₂ ⟩

    pay ≡ tea ⊎ coffee ≡ tea                                       ↝⟨ [ (λ ()) , (λ ()) ] ⟩□

    ⊥                                                              □
    where
    helper : ∀ {P} →
             machine₂ ∣ coffee ∙ [ name tea ]⟶ P →
             pay ≡ tea ⊎ coffee ≡ tea
    helper (par-right tr) = inj₂ $ cancel-name $ ·-only tr
    helper (par-left  tr) =
      inj₁ $ cancel-name $
        !-only (⊕-only (⊕-only ·-only ·-only) ·-only) tr
