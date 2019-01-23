------------------------------------------------------------------------
-- "Equational" reasoning combinator setup
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe --sized-types #-}

open import Labelled-transition-system

module Bisimilarity.Weak.Alternative.Equational-reasoning-instances
         {ℓ} {lts : LTS ℓ} where

open import Prelude

open import Bisimilarity lts
import Bisimilarity.Equational-reasoning-instances
open import Bisimilarity.Weak.Alternative lts
open import Equational-reasoning

instance

  trans∼≈ : ∀ {i} → Transitive _∼_ [ i ]_≈_
  trans∼≈ = is-transitive (transitive {a = ℓ} ∘ ∼⇒≈)

  trans∼′≈ : ∀ {i} → Transitive _∼′_ [ i ]_≈_
  trans∼′≈ = is-transitive (transitive {a = ℓ} ∘ ∼⇒≈″)

  trans∼′≈′ : ∀ {i} → Transitive _∼′_ [ i ]_≈′_
  trans∼′≈′ = is-transitive (transitive {a = ℓ} ∘ ∼⇒≈″)

  trans∼≈′ : ∀ {i} → Transitive _∼_ [ i ]_≈′_
  trans∼≈′ {i} = is-transitive (transitive {a = ℓ} ∘ ∼⇒≈ {i})

  convert∼≈ : Convertible _∼_ _≈_
  convert∼≈ = is-convertible ∼⇒≈

  convert∼′≈ : Convertible _∼′_ _≈_
  convert∼′≈ = is-convertible (convert {a = ℓ} ∘ ∼⇒≈″)

  convert∼≈′ : Convertible _∼_ _≈′_
  convert∼≈′ = is-convertible ∼⇒≈′

  convert∼′≈′ : Convertible _∼′_ _≈′_
  convert∼′≈′ = is-convertible ∼⇒≈″

open Bisimilarity.Equational-reasoning-instances
       {lts = weak lts} public
