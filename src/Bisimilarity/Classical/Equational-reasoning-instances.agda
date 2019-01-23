------------------------------------------------------------------------
-- "Equational" reasoning combinator setup
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe --sized-types #-}

open import Prelude

open import Labelled-transition-system

module Bisimilarity.Classical.Equational-reasoning-instances
         {ℓ} {lts : LTS ℓ} where

open import Bisimilarity.Classical lts

open import Equational-reasoning

instance

  reflexive∼ : Reflexive _∼_
  reflexive∼ = is-reflexive reflexive-∼

  symmetric∼ : Symmetric _∼_
  symmetric∼ = is-symmetric symmetric-∼

  trans∼∼ : Transitive _∼_ _∼_
  trans∼∼ = is-transitive transitive-∼

  convert∼∼ : Convertible _∼_ _∼_
  convert∼∼ = is-convertible id
