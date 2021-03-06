------------------------------------------------------------------------
-- "Equational" reasoning combinator setup
------------------------------------------------------------------------

{-# OPTIONS --sized-types #-}

open import Prelude

open import Labelled-transition-system

module Similarity.Weak.Equational-reasoning-instances
         {ℓ} {lts : LTS ℓ} where

open import Bisimilarity lts
open import Bisimilarity.Weak lts
import Bisimilarity.Weak.Equational-reasoning-instances
open import Equational-reasoning
open import Expansion lts
import Expansion.Equational-reasoning-instances
open import Similarity lts
open import Similarity.Weak lts

instance

  reflexive≼ : ∀ {i} → Reflexive [ i ]_≼_
  reflexive≼ = is-reflexive reflexive-≼

  reflexive≼′ : ∀ {i} → Reflexive [ i ]_≼′_
  reflexive≼′ = is-reflexive reflexive-≼′

  convert≼≼ : ∀ {i} → Convertible [ i ]_≼_ [ i ]_≼_
  convert≼≼ = is-convertible id

  convert≼′≼ : ∀ {i} → Convertible _≼′_ [ i ]_≼_
  convert≼′≼ = is-convertible λ p≼′q → force p≼′q

  convert≼≼′ : ∀ {i} → Convertible [ i ]_≼_ [ i ]_≼′_
  convert≼≼′ {i} = is-convertible lemma
    where
    lemma : ∀ {p q} → [ i ] p ≼ q → [ i ] p ≼′ q
    force (lemma p≼q) = p≼q

  convert≼′≼′ : ∀ {i} → Convertible [ i ]_≼′_ [ i ]_≼′_
  convert≼′≼′ = is-convertible id

  convert≤≼ : ∀ {i} → Convertible [ i ]_≤_ [ i ]_≼_
  convert≤≼ = is-convertible ≤⇒≼

  convert≤′≼ : ∀ {i} → Convertible _≤′_ [ i ]_≼_
  convert≤′≼ = is-convertible (convert ∘ ≤⇒≼′)

  convert≤≼′ : ∀ {i} → Convertible [ i ]_≤_ [ i ]_≼′_
  convert≤≼′ {i} = is-convertible lemma
    where
    lemma : ∀ {p q} → [ i ] p ≤ q → [ i ] p ≼′ q
    force (lemma p≤q) = convert p≤q

  convert≤′≼′ : ∀ {i} → Convertible [ i ]_≤′_ [ i ]_≼′_
  convert≤′≼′ = is-convertible ≤⇒≼′

  convert≈≼ : ∀ {i} → Convertible [ i ]_≈_ [ i ]_≼_
  convert≈≼ = is-convertible ≈⇒≼

  convert≈′≼ : ∀ {i} → Convertible _≈′_ [ i ]_≼_
  convert≈′≼ = is-convertible (convert ∘ ≈⇒≼′)

  convert≈≼′ : ∀ {i} → Convertible [ i ]_≈_ [ i ]_≼′_
  convert≈≼′ {i} = is-convertible lemma
    where
    lemma : ∀ {p q} → [ i ] p ≈ q → [ i ] p ≼′ q
    force (lemma p≈q) = convert p≈q

  convert≈′≼′ : ∀ {i} → Convertible [ i ]_≈′_ [ i ]_≼′_
  convert≈′≼′ = is-convertible ≈⇒≼′

  convert∼≼ : ∀ {i} → Convertible [ i ]_∼_ [ i ]_≼_
  convert∼≼ = is-convertible (≈⇒≼ ∘ convert {a = ℓ})

  convert∼′≼ : ∀ {i} → Convertible _∼′_ [ i ]_≼_
  convert∼′≼ = is-convertible (convert ∘ ≈⇒≼′ ∘ convert {a = ℓ})

  convert∼≼′ : ∀ {i} → Convertible [ i ]_∼_ [ i ]_≼′_
  convert∼≼′ {i} = is-convertible lemma
    where
    lemma : ∀ {p q} → [ i ] p ∼ q → [ i ] p ≼′ q
    force (lemma p∼q) = ≈⇒≼ (convert {a = ℓ} p∼q)

  convert∼′≼′ : ∀ {i} → Convertible [ i ]_∼′_ [ i ]_≼′_
  convert∼′≼′ = is-convertible (≈⇒≼′ ∘ convert {a = ℓ})

  trans≼≼ : ∀ {i} → Transitive′ [ i ]_≼_ _≼_
  trans≼≼ = is-transitive transitive-≼

  trans≼′≼ : Transitive′ _≼′_ _≼_
  trans≼′≼ = is-transitive transitive-≼′

  trans≼′≼′ : ∀ {i} → Transitive′ [ i ]_≼′_ _≼′_
  trans≼′≼′ = is-transitive (λ p≼q → transitive-≼′ p≼q ∘ convert)

  trans≼≼′ : ∀ {i} → Transitive′ [ i ]_≼_ _≼′_
  trans≼≼′ = is-transitive (λ p≼q → transitive-≼ p≼q ∘ convert)

  trans≳≼ : ∀ {i} → Transitive [ i ]_≳_ [ i ]_≼_
  trans≳≼ = is-transitive transitive-≳≼

  trans≳′≼ : ∀ {i} → Transitive _≳′_ [ i ]_≼_
  trans≳′≼ = is-transitive (transitive-≳≼ ∘ convert {a = ℓ})

  trans≳′≼′ : ∀ {i} → Transitive [ i ]_≳′_ [ i ]_≼′_
  trans≳′≼′ = is-transitive transitive-≳≼′

  trans≳≼′ : ∀ {i} → Transitive [ i ]_≳_ [ i ]_≼′_
  trans≳≼′ = is-transitive (transitive-≳≼′ ∘ convert {a = ℓ})
