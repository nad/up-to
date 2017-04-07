------------------------------------------------------------------------
-- "Equational" reasoning combinator setup
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

open import Labelled-transition-system

module Bisimilarity.Weak.Coinductive.Equational-reasoning-instances
         {lts : LTS} where

open import Prelude

open import Bisimilarity.Coinductive lts
import Bisimilarity.Coinductive.Equational-reasoning-instances
open import Bisimilarity.Weak.Coinductive lts
open import Equational-reasoning

instance

  trans∼≈ : ∀ {i} → Transitive _∼_ [ i ]_≈_
  trans∼≈ = is-transitive (transitive ∘ ∼⇒≈)

  trans∼′≈ : ∀ {i} → Transitive _∼′_ [ i ]_≈_
  trans∼′≈ = is-transitive (transitive ∘ ∼⇒≈″)

  trans∼′≈′ : ∀ {i} → Transitive _∼′_ [ i ]_≈′_
  trans∼′≈′ = is-transitive (transitive ∘ ∼⇒≈″)

  trans∼≈′ : ∀ {i} → Transitive _∼_ [ i ]_≈′_
  trans∼≈′ {i} = is-transitive (transitive ∘ ∼⇒≈ {i})

  convert∼≈ : Convertible _∼_ _≈_
  convert∼≈ = is-convertible ∼⇒≈

  convert∼′≈ : Convertible _∼′_ _≈_
  convert∼′≈ = is-convertible (convert ∘ ∼⇒≈″)

  convert∼≈′ : Convertible _∼_ _≈′_
  convert∼≈′ = is-convertible ∼⇒≈′

  convert∼′≈′ : Convertible _∼′_ _≈′_
  convert∼′≈′ = is-convertible ∼⇒≈″

open Bisimilarity.Coinductive.Equational-reasoning-instances
       {lts = weak lts} public
