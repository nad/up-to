------------------------------------------------------------------------
-- An alternative (non-standard) classical definition of weak
-- bisimilarity
------------------------------------------------------------------------

-- This definition is based on the function "wb" in Section 6.5.1 of
-- Pous and Sangiorgi's "Enhancements of the bisimulation proof
-- method".

{-# OPTIONS --without-K --safe --sized-types #-}

open import Labelled-transition-system

module Bisimilarity.Weak.Alternative.Classical {ℓ} (lts : LTS ℓ) where

open import Prelude

import Bisimilarity.Classical

open LTS lts

-- We get weak bisimilarity by instantiating strong bisimilarity with
-- a different LTS.

private
  module WB = Bisimilarity.Classical (weak lts)

open WB public
  using (⟪_,_⟫)
  renaming ( Bisimulation  to Weak-bisimulation
           ; Bisimilarity′ to Weak-bisimilarity′
           ; Bisimilarity  to Weak-bisimilarity
           ; _∼_           to _≈_
           )
