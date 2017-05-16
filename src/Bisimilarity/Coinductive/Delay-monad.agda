------------------------------------------------------------------------
-- Some results related to strong bisimilarity for the delay monad
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Bisimilarity.Coinductive.Delay-monad {A : Set} where

open import Delay-monad
open import Delay-monad.Strong-bisimilarity as DS
  using (Strongly-bisimilar; ∞Strongly-bisimilar; force)
open import Equality.Propositional
open import Logical-equivalence using (_⇔_)
open import Prelude

open import Function-universe equality-with-J hiding (id; _∘_)

open import Labelled-transition-system
open import Labelled-transition-system.Delay-monad A

open import Bisimilarity.Coinductive delay-monad
import Bisimilarity.Coinductive.Equational-reasoning-instances
open import Equational-reasoning

------------------------------------------------------------------------
-- The direct and the indirect definitions of strong bisimilarity are
-- pointwise logically equivalent

-- An emulation of the constructor DS.later-cong.

later-cong : ∀ {i x y} →
             [ i ] force x ∼′ force y → [ i ] later x ∼ later y
later-cong x∼′y =
  ⟨ (λ { later⟶ → _ , later⟶ , x∼′y })
  , (λ { later⟶ → _ , later⟶ , x∼′y })
  ⟩

mutual

  -- The direct definition of strong bisimilarity is contained in the
  -- one obtained from the transition relation.

  direct→indirect : ∀ {i x y} →
                    Strongly-bisimilar i x y → [ i ] x ∼ y
  direct→indirect DS.now-cong       = reflexive
  direct→indirect (DS.later-cong p) = later-cong (direct→indirect′ p)

  direct→indirect′ : ∀ {i x y} →
                     ∞Strongly-bisimilar i x y → [ i ] x ∼′ y
  force (direct→indirect′ p) = direct→indirect (force p)

mutual

  -- The definition of strong bisimilarity obtained from the
  -- transition relation is contained in the direct one.

  indirect→direct : ∀ {i} x y → [ i ] x ∼ y → Strongly-bisimilar i x y
  indirect→direct (now x) (now y) nx∼ny
    with left-to-right nx∼ny now⟶
  ... | _ , now⟶ , _ = DS.now-cong

  indirect→direct (later x) (later y) lx∼ly
    with left-to-right lx∼ly later⟶
  ... | _ , later⟶ , x∼′y  = DS.later-cong (∞indirect→direct x∼′y)

  indirect→direct (now x) (later y) nx∼ly
    with left-to-right nx∼ly now⟶
  ... | _ , () , _

  indirect→direct (later x) (now y) lx∼ny
    with left-to-right lx∼ny later⟶
  ... | _ , () , _

  ∞indirect→direct : ∀ {i x y} →
                     [ i ] x ∼′ y → ∞Strongly-bisimilar i x y
  force (∞indirect→direct p) = indirect→direct _ _ (force p)

-- The direct definition of the expansion relation is logically
-- equivalent to the one obtained from the transition relation.
--
-- TODO: Are the two definitions isomorphic?

direct⇔indirect : ∀ {i x y} → Strongly-bisimilar i x y ⇔ [ i ] x ∼ y
direct⇔indirect = record
  { to   = direct→indirect
  ; from = indirect→direct _ _
  }
