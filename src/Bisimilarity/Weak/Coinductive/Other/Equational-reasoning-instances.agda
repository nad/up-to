------------------------------------------------------------------------
-- "Equational" reasoning combinator setup
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

open import Labelled-transition-system

module
  Bisimilarity.Weak.Coinductive.Other.Equational-reasoning-instances
    {lts : LTS} where

open import Prelude

open import Bisimilarity.Coinductive lts
import Bisimilarity.Coinductive.Equational-reasoning-instances
open import Bisimilarity.Weak.Coinductive.Other lts
open import Equational-reasoning

instance

  reflexive≈ : ∀ {i} → Reflexive [ i ]_≈_
  reflexive≈ = is-reflexive reflexive-≈

  reflexive≈′ : ∀ {i} → Reflexive [ i ]_≈′_
  reflexive≈′ = is-reflexive reflexive-≈′

  symmetric≈ : ∀ {i} → Symmetric [ i ]_≈_
  symmetric≈ = is-symmetric symmetric-≈

  symmetric≈′ : ∀ {i} → Symmetric [ i ]_≈′_
  symmetric≈′ = is-symmetric symmetric-≈′

  convert≈≈ : ∀ {i} → Convertible [ i ]_≈_ [ i ]_≈_
  convert≈≈ = is-convertible id

  convert≈′≈ : ∀ {i} → Convertible [ ssuc i ]_≈′_ [ i ]_≈_
  convert≈′≈ = is-convertible (λ p≈′q → [_]_≈′_.force p≈′q)

  convert≈≈′ : ∀ {i} → Convertible [ i ]_≈_ [ i ]_≈′_
  convert≈≈′ {i} = is-convertible lemma
    where
    lemma : ∀ {p q} → [ i ] p ≈ q → [ i ] p ≈′ q
    [_]_≈′_.force (lemma p≈q) = p≈q

  convert≈′≈′ : ∀ {i} → Convertible [ i ]_≈′_ [ i ]_≈′_
  convert≈′≈′ = is-convertible id

  convert∼≈ : ∀ {i} → Convertible [ i ]_∼_ [ i ]_≈_
  convert∼≈ = is-convertible ∼⇒≈

  convert∼′≈ : ∀ {i} → Convertible [ ssuc i ]_∼′_ [ i ]_≈_
  convert∼′≈ = is-convertible (convert ∘ ∼⇒≈′)

  convert∼≈′ : ∀ {i} → Convertible [ i ]_∼_ [ i ]_≈′_
  convert∼≈′ {i} = is-convertible lemma
    where
    lemma : ∀ {p q} → [ i ] p ∼ q → [ i ] p ≈′ q
    [_]_≈′_.force (lemma p∼q) = ∼⇒≈ p∼q

  convert∼′≈′ : ∀ {i} → Convertible [ i ]_∼′_ [ i ]_≈′_
  convert∼′≈′ = is-convertible ∼⇒≈′

  trans≈≈ : Transitive _≈_ _≈_
  trans≈≈ = is-transitive transitive-≈

  trans≈′≈ : Transitive _≈′_ _≈_
  trans≈′≈ = is-transitive λ p≈′q → transitive ([_]_≈′_.force p≈′q)

  trans≈′≈′ : Transitive _≈′_ _≈′_
  trans≈′≈′ = is-transitive λ p≈′q q≈′r →
    transitive-≈′ p≈′q (convert q≈′r)

  trans≈≈′ : Transitive _≈_ _≈′_
  trans≈≈′ = is-transitive λ p≈q q≈′r →
    transitive-≈′ (convert p≈q) (convert q≈′r)

  trans∼≈ : ∀ {i} → Transitive _∼_ [ i ]_≈_
  trans∼≈ = is-transitive transitive-∼≈

  trans∼′≈ : ∀ {i} → Transitive _∼′_ [ i ]_≈_
  trans∼′≈ = is-transitive (transitive-∼≈ ∘ convert)

  trans∼′≈′ : ∀ {i} → Transitive _∼′_ [ i ]_≈′_
  trans∼′≈′ {i} = is-transitive lemma
    where
    lemma : ∀ {p q r} → p ∼′ q → [ i ] q ≈′ r → [ i ] p ≈′ r
    [_]_≈′_.force (lemma p∼′q q≈′r) =
      transitive-∼≈ (convert p∼′q) (convert q≈′r)

  trans∼≈′ : ∀ {i} → Transitive _∼_ [ i ]_≈′_
  trans∼≈′ {i} = is-transitive lemma
    where
    lemma : ∀ {p q r} → p ∼ q → [ i ] q ≈′ r → [ i ] p ≈′ r
    [_]_≈′_.force (lemma p∼q q≈′r) =
      transitive-∼≈ p∼q (convert q≈′r)

  trans≈∼ : ∀ {i} → Transitive′ [ i ]_≈_ _∼_
  trans≈∼ = is-transitive transitive-≈∼

  trans≈∼′ : ∀ {i} → Transitive′ [ i ]_≈_ _∼′_
  trans≈∼′ = is-transitive (λ p≈q q∼′r →
    transitive-≈∼ p≈q (convert q∼′r))

  trans≈′∼′ : ∀ {i} → Transitive′ [ i ]_≈′_ _∼′_
  trans≈′∼′ = is-transitive transitive-≈∼′

  trans≈′∼ : ∀ {i} → Transitive′ [ i ]_≈′_ _∼_
  trans≈′∼ = is-transitive λ p≈′q q∼r →
    transitive-≈∼′ p≈′q (convert q∼r)
