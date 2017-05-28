------------------------------------------------------------------------
-- Lemmas related to strong similarity for CCS
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Similarity.Strong.CCS {Name : Set} where

open import Equality.Propositional
open import Prelude

open import Function-universe equality-with-J hiding (id; _∘_)

import Bisimilarity.Coinductive.Equational-reasoning-instances
import Bisimilarity.Exercises.Coinductive.CCS as BE
open import Equational-reasoning
open import Labelled-transition-system.CCS Name
import Similarity.Strong.Equational-reasoning-instances

open import Bisimilarity.Coinductive CCS as B using (_∼_; _∼′_)
open import Similarity.Strong CCS

------------------------------------------------------------------------
-- Congruence lemmas

private
  module CL {i} = BE.Cong-lemmas [ i ]_≤′_ challenge

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

_·-cong_ : ∀ {i μ μ′ P P′} →
           μ ≡ μ′ → [ i ] P ≤ P′ → [ i ] μ · P ≤ μ′ · P′
_·-cong_ {i} {μ} {P = P} {P′} refl P≤P′ = ⟨ CL.·-cong P≤P′ ⟩

_·-cong′_ : ∀ {i μ μ′ P P′} →
            μ ≡ μ′ → [ i ] P ≤′ P′ → [ i ] μ · P ≤′ μ′ · P′
force (μ≡μ′ ·-cong′ P≤P′) = μ≡μ′ ·-cong force P≤P′

-- _· turns equal actions into similar processes.

infix 12 _·-cong _·-cong′

_·-cong : ∀ {μ μ′} → μ ≡ μ′ → μ · ≤ μ′ ·
refl ·-cong = reflexive

_·-cong′ : ∀ {μ μ′} → μ ≡ μ′ → μ · ≤′ μ′ ·
refl ·-cong′ = reflexive

mutual

  -- ν preserves similarity.

  ν-cong : ∀ {i a a′ P P′} →
           a ≡ a′ → [ i ] P ≤ P′ → [ i ] ν a P ≤ ν a′ P′
  ν-cong refl P≤P′ = ⟨ CL.ν-cong (ν-cong′ refl) P≤P′ ⟩

  ν-cong′ : ∀ {i a a′ P P′} →
            a ≡ a′ → [ i ] P ≤′ P′ → [ i ] ν a P ≤′ ν a′ P′
  force (ν-cong′ a≡a′ P≤P′) = ν-cong a≡a′ (force P≤P′)

mutual

  -- !_ preserves similarity.

  infix 10 !-cong_ !-cong′_

  !-cong_ : ∀ {i P P′} →
            [ i ] P ≤ P′ → [ i ] ! P ≤ ! P′
  !-cong P≤P′ = ⟨ CL.!-cong BE.6-1-3-2 _∣-cong′_ !-cong′_ P≤P′ ⟩

  !-cong′_ : ∀ {i P P′} → [ i ] P ≤′ P′ → [ i ] ! P ≤′ ! P′
  force (!-cong′ P≤P′) = !-cong force P≤P′

-- _[_] preserves similarity.

infix 5 _[_]-cong _[_]-cong′

_[_]-cong :
  ∀ {i n Ps Qs}
  (C : Context n) → (∀ x → [ i ] Ps x ≤ Qs x) →
  [ i ] C [ Ps ] ≤ C [ Qs ]
_[_]-cong = CL.[]-cong _∣-cong_ _⊕-cong_ _·-cong_ ν-cong !-cong_

_[_]-cong′ :
  ∀ {i n Ps Qs}
  (C : Context n) → (∀ x → [ i ] Ps x ≤′ Qs x) →
  [ i ] C [ Ps ] ≤′ C [ Qs ]
force (C [ Ps≤Qs ]-cong′) = C [ (λ x → force (Ps≤Qs x)) ]-cong

------------------------------------------------------------------------
-- Other results

-- P is similar to P ⊕ Q.

≤-⊕-left : ∀ {i P Q} → [ i ] P ≤ P ⊕ Q
≤-⊕-left = ⟨ (λ P⟶P′ → _ , choice-left P⟶P′ , reflexive) ⟩

-- Q is similar to P ⊕ Q.

≤-⊕-right : ∀ {i P Q} → [ i ] Q ≤ P ⊕ Q
≤-⊕-right = ⟨ (λ Q⟶Q′ → _ , choice-right Q⟶Q′ , reflexive) ⟩

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

  machine₁ machine₂ machine₁′ machine₂′ : Proc

  machine₁′ = name pay · (coffee · ⊕ tea ·)
  machine₁  = ! machine₁′

  machine₂′ = (name pay · (coffee ·) ⊕ name pay · (tea ·))
                ⊕
              machine₁′
  machine₂  = ! machine₂′

  -- A lemma.

  machine₁⟶ :
    ∀ {P μ} → machine₁ [ μ ]⟶ P →
    μ ≡ name pay × P ∼ machine₁ ∣ (coffee · ⊕ tea ·)
  machine₁⟶ tr = case BE.6-1-3-2 tr of λ where
    (inj₁ (_ , action , P∼))                 → refl , P∼
    (inj₂ (_ , _ , _ , _ , action , tr , _)) →
      ⊥-elim (names-are-not-inverted tr)

  -- The first machine is similar to the second one.

  machine₁≤machine₂ : ∀ {i} → [ i ] machine₁ ≤ machine₂
  machine₁≤machine₂ {i} =
    S̲t̲e̲p̲.⟨ (λ {P} tr →
              case machine₁⟶ tr of λ where
                (refl , P∼) →
                    _
                  , (machine₂                      [ name pay ]⟶⟨ replication (par-right (choice-right action)) ⟩
                     machine₂ ∣ coffee · ⊕ tea ·)
                  , (P                            ∼⟨ ≤: convert P∼ ⟩
                     machine₁ ∣ coffee · ⊕ tea ·  ∼⟨ machine₁≤′machine₂ ∣-cong′ (_ ■) ⟩■
                     machine₂ ∣ coffee · ⊕ tea ·))
         ⟩
    where
    machine₁≤′machine₂ : [ i ] machine₁ ≤′ machine₂
    force machine₁≤′machine₂ = machine₁≤machine₂

  -- The second machine is similar to the first one.

  machine₂≤machine₁ : ∀ {i} → [ i ] machine₂ ≤ machine₁
  machine₂≤machine₁ {i} = S̲t̲e̲p̲.⟨ helper ∘ BE.6-1-3-2 ⟩
    where
    machine₂≤′machine₁ : [ i ] machine₂ ≤′ machine₁
    force machine₂≤′machine₁ = machine₂≤machine₁

    lemma =
      machine₁                     [ name pay ]⟶⟨ replication (par-right action) ⟩
      machine₁ ∣ coffee · ⊕ tea ·

    helper :
      ∀ {P μ} →
      (∃ λ P′ → machine₂′ [ μ ]⟶ P′ × P ∼ machine₂ ∣ P′)
        ⊎
      (μ ≡ τ × ∃ λ P′ → ∃ λ P″ → ∃ λ a →
       machine₂′ [ name a ]⟶ P′ × machine₂′ [ name (co a) ]⟶ P″ ×
       P ∼ (machine₂ ∣ P′) ∣ P″) →
      ∃ λ Q → machine₁ [ μ ]⟶ Q × [ i ] P ≤′ Q
    helper {P} (inj₁ (_ , choice-left (choice-left action) , P∼)) =
        _
      , lemma
      , (P                            ∼⟨ ≤: convert P∼ ⟩
         machine₂ ∣ coffee ·          ∼⟨ machine₂≤′machine₁ ∣-cong′ convert ≤-⊕-left ⟩■
         machine₁ ∣ coffee · ⊕ tea ·)

    helper {P} (inj₁ (_ , choice-left (choice-right action) , P∼)) =
        _
      , lemma
      , (P                            ∼⟨ ≤: convert P∼ ⟩
         machine₂ ∣ tea ·             ∼⟨ machine₂≤′machine₁ ∣-cong′ convert ≤-⊕-right ⟩■
         machine₁ ∣ coffee · ⊕ tea ·)

    helper {P} (inj₁ (_ , choice-right action , P∼)) =
        _
      , lemma
      , (P                            ∼⟨ ≤: convert P∼ ⟩
         machine₂ ∣ coffee · ⊕ tea ·  ∼⟨ machine₂≤′machine₁ ∣-cong′ (_ ■) ⟩■
         machine₁ ∣ coffee · ⊕ tea ·)

    helper (inj₂ (_ , _ , _ , _ , choice-left (choice-left action)  , choice-left (choice-left tr)  , _)) = ⊥-elim (names-are-not-inverted tr)
    helper (inj₂ (_ , _ , _ , _ , choice-left (choice-left action)  , choice-left (choice-right tr) , _)) = ⊥-elim (names-are-not-inverted tr)
    helper (inj₂ (_ , _ , _ , _ , choice-left (choice-left action)  , choice-right tr               , _)) = ⊥-elim (names-are-not-inverted tr)
    helper (inj₂ (_ , _ , _ , _ , choice-left (choice-right action) , choice-left (choice-left tr)  , _)) = ⊥-elim (names-are-not-inverted tr)
    helper (inj₂ (_ , _ , _ , _ , choice-left (choice-right action) , choice-left (choice-right tr) , _)) = ⊥-elim (names-are-not-inverted tr)
    helper (inj₂ (_ , _ , _ , _ , choice-left (choice-right action) , choice-right tr               , _)) = ⊥-elim (names-are-not-inverted tr)
    helper (inj₂ (_ , _ , _ , _ , choice-right action               , choice-left (choice-left tr)  , _)) = ⊥-elim (names-are-not-inverted tr)
    helper (inj₂ (_ , _ , _ , _ , choice-right action               , choice-left (choice-right tr) , _)) = ⊥-elim (names-are-not-inverted tr)
    helper (inj₂ (_ , _ , _ , _ , choice-right action               , choice-right tr               , _)) = ⊥-elim (names-are-not-inverted tr)

  -- The two machines are not bisimilar.

  machine₁≁machine₂ : ¬ machine₁ ∼ machine₂
  machine₁≁machine₂ =
    machine₁ ∼ machine₂                                            ↝⟨ (λ hyp → B.right-to-left hyp
                                                                                 (replication
                                                                                    (par-right (choice-left (choice-left action))))) ⟩

    (∃ λ P → machine₁ [ name pay ]⟶ P × P ∼′ machine₂ ∣ coffee ·)  ↝⟨ Σ-map id (Σ-map (proj₂ ∘ machine₁⟶) id) ⟩

    (∃ λ P → P ∼ machine₁ ∣ (coffee · ⊕ tea ·) ×
             P ∼′ machine₂ ∣ coffee ·)                             ↝⟨ (λ { (_ , P∼ , P∼′) → transitive (symmetric P∼) (convert P∼′) }) ⟩

    machine₁ ∣ (coffee · ⊕ tea ·) ∼ machine₂ ∣ coffee ·            ↝⟨ (λ hyp → Σ-map id proj₁ $
                                                                                 B.left-to-right hyp (par-right (choice-right action))) ⟩

    (∃ λ P → machine₂ ∣ coffee · [ name tea ]⟶ P)                  ↝⟨ helper ∘ proj₂ ⟩

    pay ≡ tea ⊎ coffee ≡ tea                                       ↝⟨ [ (λ ()) , (λ ()) ] ⟩□

    ⊥                                                              □
    where
    helper : ∀ {P} →
             machine₂ ∣ coffee · [ name tea ]⟶ P →
             pay ≡ tea ⊎ coffee ≡ tea
    helper (par-right tr) = inj₂ $ cancel-name $ ·-only tr
    helper (par-left  tr) =
      inj₁ $ cancel-name $
        !-only (⊕-only (⊕-only ·-only ·-only) ·-only) tr
