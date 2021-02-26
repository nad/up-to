------------------------------------------------------------------------
-- Some results related to strong bisimilarity for the delay monad
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe --sized-types #-}

open import Prelude

module Bisimilarity.Delay-monad {a} {A : Type a} where

open import Delay-monad
open import Delay-monad.Bisimilarity as D using (force)
open import Equality.Propositional
open import Logical-equivalence using (_⇔_)

open import Function-universe equality-with-J hiding (id; _∘_)

open import Labelled-transition-system
open import Labelled-transition-system.Delay-monad A

open import Bisimilarity delay-monad
import Bisimilarity.Equational-reasoning-instances
open import Equational-reasoning

------------------------------------------------------------------------
-- The direct and the indirect definitions of strong bisimilarity are
-- pointwise logically equivalent

-- An emulation of the constructor D.later.

later-cong : ∀ {i x y} →
             [ i ] force x ∼′ force y → [ i ] later x ∼ later y
later-cong x∼′y =
  ⟨ (λ { later → _ , later , x∼′y })
  , (λ { later → _ , later , x∼′y })
  ⟩

-- The direct definition of strong bisimilarity is contained in the
-- one obtained from the transition relation.

direct→indirect : ∀ {i x y} →
                  D.[ i ] x ∼ y → [ i ] x ∼ y
direct→indirect D.now       = reflexive
direct→indirect (D.later p) = later-cong λ { .force →
                                direct→indirect (force p) }

-- The definition of strong bisimilarity obtained from the transition
-- relation is contained in the direct one.

indirect→direct : ∀ {i} x y → [ i ] x ∼ y → D.[ i ] x ∼ y
indirect→direct (now x) (now y) nx∼ny
  with left-to-right nx∼ny now
... | _ , now , _ = D.now

indirect→direct (later x) (later y) lx∼ly
  with left-to-right lx∼ly later
... | _ , later , x∼′y  = D.later λ { .force →
                            indirect→direct _ _ (force x∼′y) }

indirect→direct (now x) (later y) nx∼ly
  with left-to-right nx∼ly now
... | _ , () , _

indirect→direct (later x) (now y) lx∼ny
  with left-to-right lx∼ny later
... | _ , () , _

-- The direct definition of strong bisimilarity is pointwise logically
-- equivalent to the one obtained from the transition relation.
--
-- TODO: Are the two definitions isomorphic?

direct⇔indirect : ∀ {i x y} → D.[ i ] x ∼ y ⇔ [ i ] x ∼ y
direct⇔indirect = record
  { to   = direct→indirect
  ; from = indirect→direct _ _
  }
