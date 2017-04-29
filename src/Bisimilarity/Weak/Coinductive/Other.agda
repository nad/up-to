------------------------------------------------------------------------
-- Another coinductive definition of weak bisimilarity
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

open import Labelled-transition-system

module Bisimilarity.Weak.Coinductive.Other (lts : LTS) where

open import Prelude

import Bisimilarity.Coinductive
import Bisimilarity.Coinductive.Equational-reasoning-instances
open import Equational-reasoning

open LTS lts
private
  open module SB = Bisimilarity.Coinductive lts
    using (_∼_; _∼′_; [_]_∼_; [_]_∼′_)

open import Bisimilarity.Coinductive.General lts _[_]⇒̂_ ⟶→⇒̂ public
  using (S̲t̲e̲p̲; ⟨_,_⟩; left-to-right; right-to-left; force;
         [_]_≡_; [_]_≡′_; []≡↔;
         Extensionality; extensionality)
  renaming ( [_]_∼_ to [_]_≈_
           ; [_]_∼′_ to [_]_≈′_
           ; _∼_ to _≈_
           ; _∼′_ to _≈′_
           ; _⟶⟨_⟩ʳˡ_ to _⇒̂⟨_⟩ʳˡ_
           ; _[_]⟶⟨_⟩ʳˡ_ to _[_]⇒̂⟨_⟩ʳˡ_
           ; reflexive-∼ to reflexive-≈
           ; reflexive-∼′ to reflexive-≈′
           ; ≡⇒∼ to ≡⇒≈
           ; symmetric-∼ to symmetric-≈
           ; symmetric-∼′ to symmetric-≈′
           ; ∼:_ to ≈:_
           ; ∼′:_ to ≈′:_
           )

-- Combinators that can perhaps make the code a bit nicer to read.

infix -3 _⟶⟨_⟩⇒̂_ _[_]⟶⟨_⟩⇒̂_
         lr-result-with-action lr-result-without-action
         lr-result-with-action-⟶ lr-result-without-action-⟶

_⟶⟨_⟩⇒̂_ : ∀ {i p′ q′ μ} p → p [ μ ]⟶ p′ → [ i ] p′ ≈′ q′ →
          ∃ λ p′ → p [ μ ]⇒̂ p′ × [ i ] p′ ≈′ q′
_ ⟶⟨ p⟶p′ ⟩⇒̂ p′≈′q′ = _ ⇒̂⟨ ⟶→⇒̂ p⟶p′ ⟩ʳˡ p′≈′q′

_[_]⟶⟨_⟩⇒̂_ : ∀ {i p′ q′} p μ → p [ μ ]⟶ p′ → [ i ] p′ ≈′ q′ →
             ∃ λ p′ → p [ μ ]⇒̂ p′ × [ i ] p′ ≈′ q′
_ [ _ ]⟶⟨ p⟶p′ ⟩⇒̂ p′≈′q′ = _ ⟶⟨ p⟶p′ ⟩⇒̂ p′≈′q′

lr-result-without-action :
  ∀ {i p′ q′ μ} → [ i ] p′ ≈′ q′ → ∀ q → q [ μ ]⇒̂ q′ →
  ∃ λ q′ → q [ μ ]⇒̂ q′ × [ i ] p′ ≈′ q′
lr-result-without-action p′≈′q′ _ q⇒̂q′ = _ , q⇒̂q′ , p′≈′q′

lr-result-with-action :
  ∀ {i p′ q′} → [ i ] p′ ≈′ q′ → ∀ μ q → q [ μ ]⇒̂ q′ →
  ∃ λ q′ → q [ μ ]⇒̂ q′ × [ i ] p′ ≈′ q′
lr-result-with-action p′≈′q′ _ _ q⇒̂q′ =
  lr-result-without-action  p′≈′q′ _ q⇒̂q′

lr-result-without-action-⟶ :
  ∀ {i p′ q′ μ} → [ i ] p′ ≈′ q′ → ∀ q → q [ μ ]⟶ q′ →
  ∃ λ q′ → q [ μ ]⇒̂ q′ × [ i ] p′ ≈′ q′
lr-result-without-action-⟶ p′≈′q′ _ q⟶q′ =
  p′≈′q′ ⇐̂⟨ ⟶→⇒̂ q⟶q′ ⟩ _

lr-result-with-action-⟶ :
  ∀ {i p′ q′} → [ i ] p′ ≈′ q′ → ∀ μ q → q [ μ ]⟶ q′ →
  ∃ λ q′ → q [ μ ]⇒̂ q′ × [ i ] p′ ≈′ q′
lr-result-with-action-⟶ p′≈′q′ _ _ q⟶q′ =
  lr-result-without-action-⟶  p′≈′q′ _ q⟶q′

syntax lr-result-without-action   p′≈q′   q q⇒̂q′ = p′≈q′      ⇐̂⟨ q⇒̂q′ ⟩ q
syntax lr-result-with-action      p′≈q′ μ q q⇒̂q′ = p′≈q′ [ μ ]⇐̂⟨ q⇒̂q′ ⟩ q
syntax lr-result-without-action-⟶ p′≈q′   q q⟶q′ = p′≈q′      ⟵⟨ q⟶q′ ⟩⇒̂ q
syntax lr-result-with-action-⟶    p′≈q′ μ q q⟶q′ = p′≈q′ [ μ ]⟵⟨ q⟶q′ ⟩⇒̂ q

-- Weak bisimilarity is a weak bisimulation (of a certain kind).

weak-is-weak :
  ∀ {p p′ q μ} →
  p ≈ q → p [ μ ]⇒̂ p′ →
  ∃ λ q′ → q [ μ ]⇒̂ q′ × p′ ≈ q′
weak-is-weak = is-weak S̲t̲e̲p̲.left-to-right (λ p≈′q → force p≈′q) ⇒̂→⇒ id

mutual

  -- Weak bisimilarity is transitive.
  --
  -- Note that the transitivity proof is not claimed to be
  -- size-preserving. For proofs showing that transitivity cannot, in
  -- general, be size-preserving in any of its arguments, see
  -- Bisimilarity.Weak.Delay-monad.size-preserving-transitivityʳ⇔uninhabited
  -- and size-preserving-transitivityˡ⇔uninhabited.

  transitive-≈ : ∀ {i p q r} → p ≈ q → q ≈ r → [ i ] p ≈ r
  transitive-≈ {i} = λ p≈q q≈r →
    S̲t̲e̲p̲.⟨ lr p≈q q≈r
         , Σ-map id (Σ-map id symmetric-≈′) ∘
           lr (symmetric-≈ q≈r) (symmetric-≈ p≈q)
         ⟩
    where
    lr : ∀ {p p′ q r μ} →
         p ≈ q → q ≈ r → p [ μ ]⟶ p′ →
         ∃ λ r′ → r [ μ ]⇒̂ r′ × [ i ] p′ ≈′ r′
    lr p≈q q≈r p⟶p′ =
      let q′ , q⇒̂q′ , p′≈′q′ = S̲t̲e̲p̲.left-to-right p≈q p⟶p′
          r′ , r⇒̂r′ , q′≈r′  = weak-is-weak q≈r q⇒̂q′
      in r′ , r⇒̂r′ , transitive-≈′ p′≈′q′ q′≈r′

  transitive-≈′ : ∀ {i p q r} → p ≈′ q → q ≈ r → [ i ] p ≈′ r
  force (transitive-≈′ p≈q q≈r) = transitive-≈ (force p≈q) q≈r

-- The following variants of transitivity are partially
-- size-preserving.

-- TODO: I guess that they cannot be fully size-preserving.

mutual

  transitive-≈∼ : ∀ {i p q r} →
                  [ i ] p ≈ q → q ∼ r → [ i ] p ≈ r
  transitive-≈∼ {i} {p} {r = r} p≈q q∼r = S̲t̲e̲p̲.⟨ lr , rl ⟩
    where
    rl : ∀ {r′ μ} → r [ μ ]⟶ r′ →
         ∃ λ p′ → p [ μ ]⇒̂ p′ × [ i ] p′ ≈′ r′
    rl r⟶r′ =
      let q′ , q⟶q′ , q′∼′r′ = SB.right-to-left q∼r r⟶r′
          p′ , p⇒̂p′ , p′≈′q′ = S̲t̲e̲p̲.right-to-left p≈q q⟶q′
      in p′ , p⇒̂p′ , transitive-≈∼′ p′≈′q′ q′∼′r′

    lr : ∀ {p′ μ} → p [ μ ]⟶ p′ →
         ∃ λ r′ → r [ μ ]⇒̂ r′ × [ i ] p′ ≈′ r′
    lr p⟶p′ =
      let q′ , q⇒̂q′ , p′≈′q′ = S̲t̲e̲p̲.left-to-right p≈q p⟶p′
          r′ , r⇒̂r′ , q′∼r′  = SB.strong-is-weak q∼r q⇒̂q′
      in r′ , r⇒̂r′ , transitive-≈∼′ p′≈′q′ (_ ∼⟨ q′∼r′ ⟩■ _)

  transitive-≈∼′ : ∀ {i p q r} →
                   [ i ] p ≈′ q → q ∼′ r → [ i ] p ≈′ r
  force (transitive-≈∼′ p≈′q q∼′r) =
    transitive-≈∼ (force p≈′q) (SB.force q∼′r)

transitive-∼≈ : ∀ {i p q r} →
                p ∼ q → [ i ] q ≈ r → [ i ] p ≈ r
transitive-∼≈ p∼q q≈r =
  symmetric-≈ (transitive-≈∼ (symmetric-≈ q≈r) (symmetric p∼q))

-- Strongly bisimilar processes are weakly bisimilar.

mutual

  ∼⇒≈ : ∀ {i p q} → [ i ] p ∼ q → [ i ] p ≈ q
  ∼⇒≈ {i} = λ p∼q →
    S̲t̲e̲p̲.⟨ Σ-map id (Σ-map id symmetric-≈′) ∘ rl (symmetric p∼q)
         , rl p∼q
         ⟩
    where
    rl : ∀ {p q q′ μ} →
         [ i ] p ∼ q → q [ μ ]⟶ q′ →
         ∃ λ p′ → p [ μ ]⇒̂ p′ × [ i ] p′ ≈′ q′
    rl p∼q q⟶q′ =
      let p′ , p⟶p′ , p′∼′q′ = SB.right-to-left p∼q q⟶q′
      in p′ , ⟶→⇒̂ p⟶p′ , ∼⇒≈′ p′∼′q′

  ∼⇒≈′ : ∀ {i p q} → [ i ] p ∼′ q → [ i ] p ≈′ q
  force (∼⇒≈′ p∼′q) = ∼⇒≈ (SB.force p∼′q)
