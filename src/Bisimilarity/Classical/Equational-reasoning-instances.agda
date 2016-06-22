------------------------------------------------------------------------
-- "Equational" reasoning combinator setup
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

open import Prelude

open import Labelled-transition-system

module Bisimilarity.Classical.Equational-reasoning-instances
         {lts : LTS} {ℓ : Level} where

open import Bisimilarity.Classical lts

open import Equational-reasoning

instance

  reflexive∼ : Reflexive [ ℓ ]_∼_
  reflexive∼ = is-reflexive reflexive-∼

  symmetric∼ : Symmetric [ ℓ ]_∼_
  symmetric∼ = is-symmetric symmetric-∼

  trans∼∼ : Transitive [ ℓ ]_∼_ [ ℓ ]_∼_
  trans∼∼ = is-transitive transitive-∼

  convert∼∼ : Convertible [ ℓ ]_∼_ [ ℓ ]_∼_
  convert∼∼ = is-convertible id
