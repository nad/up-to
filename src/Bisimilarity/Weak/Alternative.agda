------------------------------------------------------------------------
-- An alternative (non-standard) coinductive definition of weak
-- bisimilarity
------------------------------------------------------------------------

-- This definition is based on the function "wb" in Section 6.5.1 of
-- Pous and Sangiorgi's "Enhancements of the bisimulation proof
-- method".

{-# OPTIONS --without-K --safe #-}

open import Labelled-transition-system

module Bisimilarity.Weak.Alternative {ℓ} (lts : LTS ℓ) where

open import Prelude

import Bisimilarity.Coinductive
import Bisimilarity.Coinductive.Equational-reasoning-instances
open import Equational-reasoning

open LTS lts

-- We get weak bisimilarity by instantiating strong bisimilarity with
-- a different LTS.

private
  module WB = Bisimilarity.Coinductive (weak lts)

open WB public
  using ( ⟨_,_⟩
        ; [_]_≡_
        ; [_]_≡′_
        ; Extensionality
        ; force
        ; left-to-right
        ; right-to-left
        )
  renaming ( _∼_         to _≈_
           ; _∼′_        to _≈′_
           ; [_]_∼_      to [_]_≈_
           ; [_]_∼′_     to [_]_≈′_
           ; _⟶⟨_⟩ʳˡ_    to _⇒⟨_⟩ʳˡ_
           ; _[_]⟶⟨_⟩ʳˡ_ to _[_]⇒⟨_⟩ʳˡ_
           )

infix -3 lr-result-with-action lr-result-without-action

lr-result-without-action = WB.lr-result-without-action
lr-result-with-action    = WB.lr-result-with-action

syntax lr-result-without-action p′≈q′   q q⟶q′ = p′≈q′      ⇐⟨ q⟶q′ ⟩ q
syntax lr-result-with-action    p′≈q′ μ q q⟶q′ = p′≈q′ [ μ ]⇐⟨ q⟶q′ ⟩ q

-- Strongly bisimilar processes are weakly bisimilar.

private
  module SB = Bisimilarity.Coinductive lts

open SB using (_∼_; _∼′_; [_]_∼_; [_]_∼′_; force)

mutual

  ∼⇒≈ : ∀ {i p q} → p ∼ q → [ i ] p ≈ q
  ∼⇒≈ {i} = λ p∼q →
    ⟨ lr p∼q
    , Σ-map id (Σ-map id symmetric) ∘ lr (symmetric p∼q)
    ⟩
    where
    lr : ∀ {p p′ q μ} →
         p ∼ q → p [ μ ]⇒̂ p′ →
         ∃ λ q′ → q [ μ ]⇒̂ q′ × [ i ] p′ ≈′ q′
    lr p∼q p⇒̂p′ =
      Σ-map id (Σ-map id ∼⇒≈′) (SB.strong-is-weak⇒̂ p∼q p⇒̂p′)

  ∼⇒≈′ : ∀ {i p q} → p ∼ q → [ i ] p ≈′ q
  force (∼⇒≈′ p∼q) = ∼⇒≈ p∼q

∼⇒≈″ : ∀ {p q} → p ∼′ q → p ≈′ q
force (∼⇒≈″ p∼′q) = ∼⇒≈ (force p∼′q)

-- TODO: I suspect that the size isn't necessarily preserved: A weak
-- proof of a given size might require a strong proof which is much
-- larger, because a single weak transition might correspond to a
-- large number of strong transitions. I guess this has to be proved
-- for a particular LTS, or with certain assumptions about the LTS.
