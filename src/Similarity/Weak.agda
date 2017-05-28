------------------------------------------------------------------------
-- A coinductive definition of weak similarity
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

open import Labelled-transition-system

module Similarity.Weak (lts : LTS) where

open import Prelude

open import Bisimilarity.Weak.Coinductive.Other lts as WB
  using ([_]_≈_; [_]_≈′_)
open import Expansion lts as E using ([_]_≳_; [_]_≳′_)
open import Similarity.Strong lts as S using ([_]_≤_; [_]_≤′_)

open LTS lts

open import Similarity.General lts _[_]⇒̂_ ⟶→⇒̂ public
  renaming ( Similarity to Weak-similarity
           ; Similarity′ to Weak-similarity′
           ; [_]_≤_ to [_]_≼_
           ; [_]_≤′_ to [_]_≼′_
           ; _≤_ to _≼_
           ; _≤′_ to _≼′_
           ; reflexive-≤ to reflexive-≼
           ; reflexive-≤′ to reflexive-≼′
           ; ≡⇒≤ to ≡⇒≼
           ; ≤:_ to ≼:_
           ; ≤′:_ to ≼′:_
           )

mutual

  -- Weak bisimilarity is contained in weak similarity.

  ≈⇒≼ : ∀ {i p q} → [ i ] p ≈ q → [ i ] p ≼ q
  ≈⇒≼ = λ p≈q →
    ⟨ (λ q⟶q′ →
         let p′ , p⇒̂p′ , p′≈′q′ = WB.left-to-right p≈q q⟶q′
         in p′ , p⇒̂p′ , ≈⇒≼′ p′≈′q′)
    ⟩

  ≈⇒≼′ : ∀ {i p q} → [ i ] p ≈′ q → [ i ] p ≼′ q
  force (≈⇒≼′ p≳′q) = ≈⇒≼ (S.force p≳′q)

mutual

  -- Similarity is contained in weak similarity.

  ≤⇒≼ : ∀ {i p q} → [ i ] p ≤ q → [ i ] p ≼ q
  ≤⇒≼ = λ p≤q →
    ⟨ (λ q⟶q′ →
         let p′ , p⟶p′ , p′≤′q′ = S.challenge p≤q q⟶q′
         in p′ , ⟶→⇒̂ p⟶p′ , ≤⇒≼′ p′≤′q′)
    ⟩

  ≤⇒≼′ : ∀ {i p q} → [ i ] p ≤′ q → [ i ] p ≼′ q
  force (≤⇒≼′ p≳′q) = ≤⇒≼ (S.force p≳′q)

-- Weak similarity is a weak simulation (of a certain kind).

weak-is-weak :
  ∀ {p p′ q μ} →
  p ≼ q → p [ μ ]⇒̂ p′ →
  ∃ λ q′ → q [ μ ]⇒̂ q′ × p′ ≼ q′
weak-is-weak = is-weak challenge (λ p≼′q → force p≼′q) ⇒̂→⇒ id

mutual

  -- Similarity is transitive.
  --
  -- Note that the size of the second argument is not preserved.
  --
  -- TODO: Can one prove that the size cannot be preserved?

  transitive-≼ : ∀ {i p q r} → [ i ] p ≼ q → q ≼ r → [ i ] p ≼ r
  transitive-≼ p≼q q≼r =
    ⟨ (λ p⟶p′ →
         let q′ , q⇒̂q′ , p′≼q′ = challenge p≼q p⟶p′
             r′ , r⇒̂r′ , q′≼r′ = weak-is-weak q≼r q⇒̂q′
         in r′ , r⇒̂r′ , transitive-≼′ p′≼q′ q′≼r′)
    ⟩

  transitive-≼′ :
    ∀ {i p q r} → [ i ] p ≼′ q → q ≼ r → [ i ] p ≼′ r
  force (transitive-≼′ p≼q q≼r) = transitive-≼ (force p≼q) q≼r

mutual

  -- A fully size-preserving transitivity-like lemma.

  transitive-≳≼ : ∀ {i p q r} → [ i ] p ≳ q → [ i ] q ≼ r → [ i ] p ≼ r
  transitive-≳≼ p≳q q≼r =
    ⟨ (λ p⟶p′ → case E.left-to-right p≳q p⟶p′ of λ where
                  (_ , done s , p′≳q) →
                    _ , silent s done
                      , transitive-≳≼′
                          p′≳q (record { force = λ { {_} → q≼r } })

                  (q′ , step q⟶q′ , p′≳q′) →
                    let r′ , r⇒̂r′ , q′≼r′ = challenge q≼r q⟶q′
                    in r′ , r⇒̂r′ , transitive-≳≼′ p′≳q′ q′≼r′)
    ⟩

  transitive-≳≼′ :
    ∀ {i p q r} → [ i ] p ≳′ q → [ i ] q ≼′ r → [ i ] p ≼′ r
  force (transitive-≳≼′ p≼q q≼r) =
    transitive-≳≼ (force p≼q) (force q≼r)
