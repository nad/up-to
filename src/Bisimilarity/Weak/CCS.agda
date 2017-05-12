------------------------------------------------------------------------
-- A lemma related to weak bisimilarity and CCS
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Bisimilarity.Weak.CCS {Name : Set} where

open import Prelude

open import Labelled-transition-system

open CCS Name
open LTS CCS hiding (Proc; _[_]⟶_)

open import Bisimilarity.Weak.Coinductive.Other CCS
import
  Bisimilarity.Weak.Coinductive.Other.Equational-reasoning-instances
open import Equational-reasoning

-- _∣_ preserves weak bisimilarity.

mutual

  infix 6 _∣-cong-≈_ _∣-cong-≈′_

  _∣-cong-≈_ : ∀ {i P P′ Q Q′} →
               [ i ] P ≈ P′ → [ i ] Q ≈ Q′ → [ i ] P ∣ Q ≈ P′ ∣ Q′
  _∣-cong-≈_ {i} = λ P≈P′ Q≈Q′ →
    ⟨ lr P≈P′ Q≈Q′
    , Σ-map id (Σ-map id symmetric) ∘
      lr (symmetric P≈P′) (symmetric Q≈Q′)
    ⟩
    where
    lr : ∀ {P P′ Q Q′ R μ} →
         [ i ] P ≈ P′ → [ i ] Q ≈ Q′ → P ∣ Q [ μ ]⟶ R →
         ∃ λ R′ → P′ ∣ Q′ [ μ ]⇒̂ R′ × [ i ] R ≈′ R′
    lr P≈P′ Q≈Q′ (par-left tr)   = Σ-map (_∣ _)
                                         (Σ-map (map-⇒̂ par-left)
                                                (_∣-cong-≈′
                                                   convert Q≈Q′))
                                     (left-to-right P≈P′ tr)
    lr P≈P′ Q≈Q′ (par-right tr)  = Σ-map (_ ∣_)
                                         (Σ-map (map-⇒̂ par-right)
                                                (convert P≈P′
                                                   ∣-cong-≈′_))
                                     (left-to-right Q≈Q′ tr)
    lr P≈P′ Q≈Q′ (par-τ tr₁ tr₂) = Σ-zip _∣_
                                         (Σ-zip (zip-⇒̂ par-left
                                                       par-right
                                                       (λ ()) (λ _ ())
                                                       (λ ()) par-τ)
                                                _∣-cong-≈′_)
                                     (left-to-right P≈P′ tr₁)
                                     (left-to-right Q≈Q′ tr₂)

  _∣-cong-≈′_ :
    ∀ {i P P′ Q Q′} →
    [ i ] P ≈′ P′ → [ i ] Q ≈′ Q′ → [ i ] P ∣ Q ≈′ P′ ∣ Q′
  force (P≈′P′ ∣-cong-≈′ Q≈′Q′) = force P≈′P′ ∣-cong-≈ force Q≈′Q′
