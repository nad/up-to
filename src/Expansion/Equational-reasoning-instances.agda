------------------------------------------------------------------------
-- "Equational" reasoning combinator setup
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe --sized-types #-}

open import Labelled-transition-system

module Expansion.Equational-reasoning-instances {ℓ} {lts : LTS ℓ} where

open import Prelude

open import Bisimilarity lts
import Bisimilarity.Equational-reasoning-instances
open import Equational-reasoning
open import Expansion lts

instance

  reflexive≳ : ∀ {i} → Reflexive [ i ]_≳_
  reflexive≳ = is-reflexive reflexive-≳

  reflexive≳′ : ∀ {i} → Reflexive [ i ]_≳′_
  reflexive≳′ = is-reflexive reflexive-≳′

  convert≳≳ : ∀ {i} → Convertible [ i ]_≳_ [ i ]_≳_
  convert≳≳ = is-convertible id

  convert≳′≳ : ∀ {i} → Convertible _≳′_ [ i ]_≳_
  convert≳′≳ = is-convertible λ p≳′q → force p≳′q

  convert≳≳′ : ∀ {i} → Convertible [ i ]_≳_ [ i ]_≳′_
  convert≳≳′ = is-convertible lemma
    where
    lemma : ∀ {i p q} → [ i ] p ≳ q → [ i ] p ≳′ q
    force (lemma p≳q) = p≳q

  convert≳′≳′ : ∀ {i} → Convertible [ i ]_≳′_ [ i ]_≳′_
  convert≳′≳′ = is-convertible id

  convert∼≳ : ∀ {i} → Convertible [ i ]_∼_ [ i ]_≳_
  convert∼≳ = is-convertible ∼⇒≳

  convert∼′≳ : ∀ {i} → Convertible _∼′_ [ i ]_≳_
  convert∼′≳ = is-convertible (convert ∘ ∼⇒≳′)

  convert∼≳′ : ∀ {i} → Convertible [ i ]_∼_ [ i ]_≳′_
  convert∼≳′ {i} = is-convertible lemma
    where
    lemma : ∀ {p q} → [ i ] p ∼ q → [ i ] p ≳′ q
    force (lemma p∼q) = ∼⇒≳ p∼q

  convert∼′≳′ : ∀ {i} → Convertible [ i ]_∼′_ [ i ]_≳′_
  convert∼′≳′ = is-convertible ∼⇒≳′

  trans≳≳ : ∀ {i} → Transitive _≳_ [ i ]_≳_
  trans≳≳ = is-transitive transitive-≳

  trans≳′≳ : ∀ {i} → Transitive _≳′_ [ i ]_≳_
  trans≳′≳ = is-transitive λ p≳′q → transitive (force p≳′q)

  trans≳′≳′ : ∀ {i} → Transitive _≳′_ [ i ]_≳′_
  trans≳′≳′ = is-transitive transitive-≳′

  trans≳≳′ : ∀ {i} → Transitive _≳_ [ i ]_≳′_
  trans≳≳′ = is-transitive lemma
    where
    lemma : ∀ {i p q r} → p ≳ q → [ i ] q ≳′ r → [ i ] p ≳′ r
    force (lemma p≳q q≳′r) = transitive-≳ p≳q (force q≳′r)

  trans∼≳ : ∀ {i} → Transitive _∼_ [ i ]_≳_
  trans∼≳ = is-transitive transitive-∼≳

  -- The occurrences of {a = ℓ} below can perhaps be removed if
  -- Issue #2780 on the Agda bug tracker is fixed.

  trans∼′≳ : ∀ {i} → Transitive _∼′_ [ i ]_≳_
  trans∼′≳ = is-transitive (transitive-∼≳ ∘ convert {a = ℓ})

  trans∼′≳′ : ∀ {i} → Transitive _∼′_ [ i ]_≳′_
  trans∼′≳′ {i} = is-transitive lemma
    where
    lemma : ∀ {p q r} → p ∼′ q → [ i ] q ≳′ r → [ i ] p ≳′ r
    force (lemma p∼′q q≳′r) =
      transitive-∼≳ (convert {a = ℓ} p∼′q) (force q≳′r)

  trans∼≳′ : ∀ {i} → Transitive _∼_ [ i ]_≳′_
  trans∼≳′ {i} = is-transitive lemma
    where
    lemma : ∀ {p q r} → p ∼ q → [ i ] q ≳′ r → [ i ] p ≳′ r
    force (lemma p∼q q≳′r) = transitive-∼≳ p∼q (force q≳′r)

  trans≳∼ : ∀ {i} → Transitive′ [ i ]_≳_ _∼_
  trans≳∼ = is-transitive transitive-≳∼

  trans≳∼′ : ∀ {i} → Transitive′ [ i ]_≳_ _∼′_
  trans≳∼′ = is-transitive (λ p≳q q∼′r →
    transitive-≳∼ p≳q (convert {a = ℓ} q∼′r))

  trans≳′∼′ : ∀ {i} → Transitive′ [ i ]_≳′_ _∼′_
  trans≳′∼′ = is-transitive transitive-≳∼′

  trans≳′∼ : ∀ {i} → Transitive′ [ i ]_≳′_ _∼_
  trans≳′∼ = is-transitive λ p≳′q q∼r →
    transitive-≳∼′ p≳′q (convert {a = ℓ} q∼r)
