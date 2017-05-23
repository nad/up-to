------------------------------------------------------------------------
-- "Equational" reasoning combinator setup
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

open import Prelude

open import Labelled-transition-system

module Similarity.Strong.Equational-reasoning-instances
         {lts : LTS} {i : Size} where

open import Bisimilarity.Coinductive lts
open import Equational-reasoning
open import Similarity.Strong lts

instance

  reflexive≤ : Reflexive [ i ]_≤_
  reflexive≤ = is-reflexive reflexive-≤

  reflexive≤′ : Reflexive [ i ]_≤′_
  reflexive≤′ = is-reflexive reflexive-≤′

  convert≤≤ : Convertible [ i ]_≤_ [ i ]_≤_
  convert≤≤ = is-convertible id

  convert≤′≤ : Convertible [ ssuc i ]_≤′_ [ i ]_≤_
  convert≤′≤ = is-convertible λ p≤′q → force p≤′q

  convert≤≤′ : Convertible [ i ]_≤_ [ i ]_≤′_
  convert≤≤′ = is-convertible lemma
    where
    lemma : ∀ {p q} → [ i ] p ≤ q → [ i ] p ≤′ q
    force (lemma p≤q) = p≤q

  convert≤′≤′ : Convertible [ i ]_≤′_ [ i ]_≤′_
  convert≤′≤′ = is-convertible id

  convert∼≤ : Convertible [ i ]_∼_ [ i ]_≤_
  convert∼≤ = is-convertible ∼⇒≤

  convert∼′≤ : Convertible [ ssuc i ]_∼′_ [ i ]_≤_
  convert∼′≤ = is-convertible (convert ∘ ∼⇒≤′)

  convert∼≤′ : ∀ {i} → Convertible [ i ]_∼_ [ i ]_≤′_
  convert∼≤′ {i} = is-convertible lemma
    where
    lemma : ∀ {p q} → [ i ] p ∼ q → [ i ] p ≤′ q
    force (lemma p∼q) = ∼⇒≤ p∼q

  convert∼′≤′ : ∀ {i} → Convertible [ i ]_∼′_ [ i ]_≤′_
  convert∼′≤′ = is-convertible ∼⇒≤′

  trans≤≤ : Transitive [ i ]_≤_ [ i ]_≤_
  trans≤≤ = is-transitive transitive-≤

  trans≤′≤ : Transitive [ ssuc i ]_≤′_ [ i ]_≤_
  trans≤′≤ = is-transitive λ p≤′q → transitive (force p≤′q)

  trans≤′≤′ : Transitive [ i ]_≤′_ [ i ]_≤′_
  trans≤′≤′ = is-transitive transitive-≤′

  trans≤≤′ : Transitive [ i ]_≤_ [ i ]_≤′_
  trans≤≤′ = is-transitive lemma
    where
    lemma : ∀ {p q r} → [ i ] p ≤ q → [ i ] q ≤′ r → [ i ] p ≤′ r
    force (lemma p≤q q≤′r) = transitive-≤ p≤q (force q≤′r)
