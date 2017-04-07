------------------------------------------------------------------------
-- A classical definition of weak bisimilarity
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

open import Labelled-transition-system

module Bisimilarity.Weak.Classical (lts : LTS) where

open import Prelude

import Bisimilarity.Classical

open LTS lts

-- We get weak bisimilarity by instantiating strong bisimilarity with
-- a different LTS.

private
  module WB = Bisimilarity.Classical (weak lts)

open WB public
  using (⟪_,_⟫)
  renaming ( Bisimulation to Weak-bisimulation
           ; _∼_          to _≈_
           ; [_]_∼_       to [_]_≈_
           )
