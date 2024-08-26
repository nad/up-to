------------------------------------------------------------------------
-- "Equational" reasoning combinator setup
------------------------------------------------------------------------

{-# OPTIONS --sized-types #-}

open import Prelude.Size

open import Labelled-transition-system

module Similarity.Equational-reasoning-instances
         {ℓ} {lts : LTS ℓ} {i : Size} where

open import Prelude

open import Bisimilarity lts
open import Equational-reasoning
open import Similarity lts

instance

  reflexive≤ : Reflexive [ i ]_≤_
  reflexive≤ = is-reflexive reflexive-≤

  reflexive≤′ : Reflexive [ i ]_≤′_
  reflexive≤′ = is-reflexive reflexive-≤′

  convert≤≤ : Convertible [ i ]_≤_ [ i ]_≤_
  convert≤≤ = is-convertible id

  convert≤′≤ : Convertible _≤′_ [ i ]_≤_
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

  convert∼′≤ : Convertible _∼′_ [ i ]_≤_
  convert∼′≤ = is-convertible (convert ∘ ∼⇒≤′)

  convert∼≤′ : Convertible [ i ]_∼_ [ i ]_≤′_
  convert∼≤′ = is-convertible lemma
    where
    lemma : ∀ {p q} → [ i ] p ∼ q → [ i ] p ≤′ q
    force (lemma p∼q) = ∼⇒≤ p∼q

  convert∼′≤′ : Convertible [ i ]_∼′_ [ i ]_≤′_
  convert∼′≤′ = is-convertible ∼⇒≤′

  trans≤≤ : Transitive [ i ]_≤_ [ i ]_≤_
  trans≤≤ = is-transitive transitive-≤

  trans≤′≤ : Transitive _≤′_ [ i ]_≤_
  trans≤′≤ = is-transitive λ p≤′q → transitive (force p≤′q)

  trans≤′≤′ : Transitive [ i ]_≤′_ [ i ]_≤′_
  trans≤′≤′ = is-transitive transitive-≤′

  trans≤≤′ : Transitive [ i ]_≤_ [ i ]_≤′_
  trans≤≤′ = is-transitive lemma
    where
    lemma : ∀ {p q r} → [ i ] p ≤ q → [ i ] q ≤′ r → [ i ] p ≤′ r
    force (lemma p≤q q≤′r) = transitive-≤ p≤q (force q≤′r)
