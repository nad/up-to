------------------------------------------------------------------------
-- The two coinductive definitions of weak bisimilarity are pointwise
-- logically equivalent
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe --sized-types #-}

open import Labelled-transition-system

module Bisimilarity.Weak.Equivalent {ℓ} {lts : LTS ℓ} where

open import Equality.Propositional
open import Logical-equivalence using (_⇔_)
open import Prelude

import Bisimilarity.Weak lts as Std
import Bisimilarity.Weak.Alternative lts as Alt
import Bisimilarity.Weak.Alternative.Equational-reasoning-instances
import Bisimilarity.Weak.Equational-reasoning-instances
open import Equational-reasoning

open LTS lts

mutual

  -- The alternative definition of weak bisimilarity can be converted
  -- to the standard one, in a size-preserving way.

  alternative⇒ : ∀ {i p q} → Alt.[ i ] p ≈ q → Std.[ i ] p ≈ q
  alternative⇒ {i} p≈q =
    Std.⟨ lr p≈q
        , Σ-map id (Σ-map id symmetric) ∘ lr (symmetric p≈q)
        ⟩
    where
    lr : ∀ {p p′ q μ} →
         Alt.[ i ] p ≈ q → p [ μ ]⟶ p′ →
         ∃ λ q′ → q [ μ ]⇒̂ q′ × Std.[ i ] p′ ≈′ q′
    lr p≈q p⟶p′ =
      Σ-map id (Σ-map id alternative⇒′)
        (Alt.left-to-right p≈q (⟶→⇒̂ p⟶p′))

  alternative⇒′ : ∀ {i p q} → Alt.[ i ] p ≈′ q → Std.[ i ] p ≈′ q
  Std.force (alternative⇒′ p≈′q) = alternative⇒ (Alt.force p≈′q)

mutual

  -- One can also convert in the other direction. Note that this
  -- conversion is not guaranteed to be size-preserving. For at least
  -- one LTS it cannot (in general) be size-preserving, see
  -- Bisimilarity.Weak.Delay-monad.size-preserving-⇒alternative⇔uninhabited.

  ⇒alternative : ∀ {i p q} → p Std.≈ q → Alt.[ i ] p ≈ q
  ⇒alternative {i} p≈q =
    Alt.⟨ lr p≈q
        , Σ-map id (Σ-map id symmetric) ∘ lr (symmetric p≈q)
        ⟩
    where
    lr : ∀ {p p′ q μ} →
         p Std.≈ q → p [ μ ]⇒̂ p′ →
         ∃ λ q′ → q [ μ ]⇒̂ q′ × Alt.[ i ] p′ ≈′ q′
    lr p≈q p⇒̂p′ =
      Σ-map id (Σ-map id ⇒alternative′) (Std.weak-is-weak⇒̂ p≈q p⇒̂p′)

  ⇒alternative′ : ∀ {i p q} → p Std.≈ q → Alt.[ i ] p ≈′ q
  Alt.force (⇒alternative′ p≈q) = ⇒alternative p≈q

-- The two definitions of weak bisimilarity are logically equivalent.

alternative⇔ : ∀ {p q} → p Alt.≈ q ⇔ p Std.≈ q
alternative⇔ = record
  { to   = alternative⇒
  ; from = ⇒alternative
  }

-- TODO: I don't know if the two definitions of weak bisimilarity are
-- isomorphic.
