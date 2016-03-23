------------------------------------------------------------------------
-- A coinductive definition of weak bisimilarity
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

open import Labelled-transition-system

module Bisimilarity.Weak.Coinductive (lts : LTS) where

open import Prelude

import Bisimilarity.Coinductive

open LTS lts

-- We get weak bisimilarity by instantiating strong bisimilarity with
-- a different LTS.

private
  module WB = Bisimilarity.Coinductive (weak lts)

open WB public
  using ( ⟨_,_⟩
        ; reflexive
        ; reflexive′
        ; symmetric
        ; symmetric′
        ; transitive
        ; transitive′
        ; [_]_≡_
        ; [_]_≡′_
        ; Extensionality
        )
  renaming ( _∼_         to _≈_
           ; _∼′_        to _≈′_
           ; [_]_∼_      to [_]_≈_
           ; [_]_∼′_     to [_]_≈′_
           ; _⟶⟨_⟩ʳˡ_    to _⇒⟨_⟩ʳˡ_
           ; _[_]⟶⟨_⟩ʳˡ_ to _[_]⇒⟨_⟩ʳˡ_
           ; _∼⟨_⟩_      to _≈⟨_⟩_
           ; _∼′⟨_⟩_     to _≈′⟨_⟩_
           ; _∼′⟨_⟩′_    to _≈′⟨_⟩′_
           ; _∼⟨_⟩′_     to _≈⟨_⟩′_
           )

infix -3 lr-result-with-action lr-result-without-action

lr-result-without-action = WB.lr-result-without-action
lr-result-with-action    = WB.lr-result-with-action

syntax lr-result-without-action p′≈q′   q q⟶q′ = p′≈q′      ⇐⟨ q⟶q′ ⟩ q
syntax lr-result-with-action    p′≈q′ μ q q⟶q′ = p′≈q′ [ μ ]⇐⟨ q⟶q′ ⟩ q

infix -1 finally-≈ finally-≈′ finally-′≈ finally-′≈′

finally-≈   = WB.finally-∼
finally-′≈  = WB.finally-′∼
finally-≈′  = WB.finally-∼′
finally-′≈′ = WB.finally-′∼′

syntax finally-≈   p q p≈q  = p ≈⟨  p≈q  ⟩∎ q
syntax finally-′≈  p q p≈′q = p ≈′⟨ p≈′q ⟩∎ q
syntax finally-≈′  p q p≈q  = p ≈⟨  p≈q  ⟩′∎ q
syntax finally-′≈′ p q p≈′q = p ≈′⟨ p≈′q ⟩′∎ q

-- Strongly bisimilar processes are weakly bisimilar.

private
  module SB = Bisimilarity.Coinductive lts

open SB using (_∼_; _∼′_; [_]_∼_; [_]_∼′_)

mutual

  ∼⇒≈ : ∀ {i p q} → p ∼ q → [ i ] p ≈ q
  ∼⇒≈ {i} = λ p∼q →
    ⟨ lr p∼q
    , Σ-map id (Σ-map id symmetric′) ∘ lr (SB.symmetric p∼q)
    ⟩
    where
    lr : ∀ {p p′ q μ} →
         p ∼ q → p [ μ ]⇒̂ p′ →
         ∃ λ q′ → q [ μ ]⇒̂ q′ × [ i ] p′ ≈′ q′
    lr p∼q p⇒̂p′ =
      Σ-map id (Σ-map id ∼⇒≈′) (SB.strong-is-weak p∼q p⇒̂p′)

  ∼⇒≈′ : ∀ {i p q} → p ∼ q → [ i ] p ≈′ q
  [_]_≈′_.force (∼⇒≈′ p∼q) = ∼⇒≈ p∼q

∼⇒≈″ : ∀ {p q} → p ∼′ q → p ≈′ q
[_]_≈′_.force (∼⇒≈″ p∼′q) = ∼⇒≈ ([_]_∼′_.force p∼′q)

-- TODO: I suspect that the size isn't necessarily preserved: A weak
-- proof of a given size might require a strong proof which is much
-- larger, because a single weak transition might correspond to a
-- large number of strong transitions. I guess this has to be proved
-- for a particular LTS, or with certain assumptions about the LTS.

-- More "equational" reasoning combinators.

infix  -1 finally-∼≈ finally-∼′≈ finally-∼≈′ finally-∼′≈′
infixr -2 _∼⟨_⟩≈_ _∼′⟨_⟩≈_ _∼′⟨_⟩≈′_ _∼⟨_⟩≈′_

_∼⟨_⟩≈_ : ∀ {i} p {q r} → p ∼ q → [ i ] q ≈ r → [ i ] p ≈ r
_ ∼⟨ p∼q ⟩≈ q≈r = _ ≈⟨ ∼⇒≈ p∼q ⟩ q≈r

_∼′⟨_⟩≈_ : ∀ {i} p {q r} → p ∼′ q → [ i ] q ≈ r → [ i ] p ≈ r
_ ∼′⟨ p∼′q ⟩≈ q≈r = _ ≈′⟨ ∼⇒≈″ p∼′q ⟩ q≈r

_∼′⟨_⟩≈′_ : ∀ {i} p {q r} → p ∼′ q → [ i ] q ≈′ r → [ i ] p ≈′ r
_ ∼′⟨ p∼′q ⟩≈′ q≈′r = _ ≈′⟨ ∼⇒≈″ p∼′q ⟩′ q≈′r

_∼⟨_⟩≈′_ : ∀ {i} p {q r} → p ∼ q → [ i ] q ≈′ r → [ i ] p ≈′ r
_ ∼⟨ p∼q ⟩≈′ q≈′r = _ ≈⟨ ∼⇒≈ p∼q ⟩′ q≈′r

finally-∼≈ : ∀ p q → p ∼ q → p ≈ q
finally-∼≈ _ _ p∼q = ∼⇒≈ p∼q

finally-∼′≈ : ∀ p q → p ∼′ q → p ≈ q
finally-∼′≈ _ _ p∼′q = _ ≈′⟨ ∼⇒≈″ p∼′q ⟩∎ _

finally-∼≈′ : ∀ p q → p ∼ q → p ≈′ q
finally-∼≈′ _ _ p∼q = ∼⇒≈′ p∼q

finally-∼′≈′ : ∀ p q → p ∼′ q → p ≈′ q
finally-∼′≈′ _ _ p∼′q = ∼⇒≈″ p∼′q

syntax finally-∼≈   p q p∼q  = p ∼⟨  p∼q  ⟩≈∎ q
syntax finally-∼′≈  p q p∼′q = p ∼′⟨ p∼′q ⟩≈∎ q
syntax finally-∼≈′  p q p∼q  = p ∼⟨  p∼q  ⟩≈′∎ q
syntax finally-∼′≈′ p q p∼′q = p ∼′⟨ p∼′q ⟩≈′∎ q
