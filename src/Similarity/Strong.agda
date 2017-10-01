------------------------------------------------------------------------
-- A coinductive definition of (strong) similarity
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Labelled-transition-system

module Similarity.Strong {ℓ} (lts : LTS ℓ) where

open import Prelude

open import Bisimilarity.Coinductive lts as SB
  using ([_]_∼_; [_]_∼′_)

open LTS lts

open import Similarity.General lts _[_]⟶_ id public

mutual

  -- Bisimilarity is contained in similarity.

  ∼⇒≤ : ∀ {i p q} → [ i ] p ∼ q → [ i ] p ≤ q
  ∼⇒≤ = λ p∼q →
    ⟨ (λ q⟶q′ →
         let p′ , p⟶p′ , p′∼′q′ = SB.left-to-right p∼q q⟶q′
         in p′ , p⟶p′ , ∼⇒≤′ p′∼′q′)
    ⟩

  ∼⇒≤′ : ∀ {i p q} → [ i ] p ∼′ q → [ i ] p ≤′ q
  force (∼⇒≤′ p≳′q) = ∼⇒≤ (SB.force p≳′q)

mutual

  -- Similarity is transitive.

  transitive-≤ : ∀ {i p q r} → [ i ] p ≤ q → [ i ] q ≤ r → [ i ] p ≤ r
  transitive-≤ p≤q q≤r =
    ⟨ (λ p⟶p′ →
         let q′ , q⟶q′ , p′≤q′ = challenge p≤q p⟶p′
             r′ , r⟶r′ , q′≤r′ = challenge q≤r q⟶q′
         in r′ , r⟶r′ , transitive-≤′ p′≤q′ q′≤r′)
    ⟩

  transitive-≤′ :
    ∀ {i p q r} → [ i ] p ≤′ q → [ i ] q ≤′ r → [ i ] p ≤′ r
  force (transitive-≤′ p≤q q≤r) = transitive-≤ (force p≤q) (force q≤r)
