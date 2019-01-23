------------------------------------------------------------------------
-- "Equational" reasoning combinator setup
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe --sized-types #-}

open import Labelled-transition-system

module Bisimilarity.Weak.Equational-reasoning-instances
         {ℓ} {lts : LTS ℓ} where

open import Prelude

open import Bisimilarity lts
import Bisimilarity.Equational-reasoning-instances
open import Bisimilarity.Weak lts
open import Equational-reasoning
open import Expansion lts
import Expansion.Equational-reasoning-instances

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

  convert≈′≈ : ∀ {i} → Convertible _≈′_ [ i ]_≈_
  convert≈′≈ = is-convertible (λ p≈′q → force p≈′q)

  convert≈≈′ : ∀ {i} → Convertible [ i ]_≈_ [ i ]_≈′_
  convert≈≈′ {i} = is-convertible lemma
    where
    lemma : ∀ {p q} → [ i ] p ≈ q → [ i ] p ≈′ q
    force (lemma p≈q) = p≈q

  convert≈′≈′ : ∀ {i} → Convertible [ i ]_≈′_ [ i ]_≈′_
  convert≈′≈′ = is-convertible id

  convert∼≈ : ∀ {i} → Convertible [ i ]_∼_ [ i ]_≈_
  convert∼≈ = is-convertible ∼⇒≈

  convert∼′≈ : ∀ {i} → Convertible _∼′_ [ i ]_≈_
  convert∼′≈ = is-convertible (convert ∘ ∼⇒≈′)

  convert∼≈′ : ∀ {i} → Convertible [ i ]_∼_ [ i ]_≈′_
  convert∼≈′ {i} = is-convertible lemma
    where
    lemma : ∀ {p q} → [ i ] p ∼ q → [ i ] p ≈′ q
    force (lemma p∼q) = ∼⇒≈ p∼q

  convert∼′≈′ : ∀ {i} → Convertible [ i ]_∼′_ [ i ]_≈′_
  convert∼′≈′ = is-convertible ∼⇒≈′

  convert≳≈ : ∀ {i} → Convertible [ i ]_≳_ [ i ]_≈_
  convert≳≈ = is-convertible ≳⇒≈

  convert≳′≈ : ∀ {i} → Convertible _≳′_ [ i ]_≈_
  convert≳′≈ = is-convertible (convert ∘ ≳⇒≈′)

  convert≳≈′ : ∀ {i} → Convertible [ i ]_≳_ [ i ]_≈′_
  convert≳≈′ {i} = is-convertible lemma
    where
    lemma : ∀ {p q} → [ i ] p ≳ q → [ i ] p ≈′ q
    force (lemma p≳q) = ≳⇒≈ p≳q

  convert≳′≈′ : ∀ {i} → Convertible [ i ]_≳′_ [ i ]_≈′_
  convert≳′≈′ = is-convertible ≳⇒≈′

  trans≈≈ : Transitive _≈_ _≈_
  trans≈≈ = is-transitive transitive-≈

  trans≈′≈ : Transitive _≈′_ _≈_
  trans≈′≈ = is-transitive λ p≈′q → transitive (force p≈′q)

  trans≈′≈′ : Transitive _≈′_ _≈′_
  trans≈′≈′ = is-transitive λ p≈′q q≈′r →
    transitive-≈′ p≈′q (convert q≈′r)

  trans≈≈′ : Transitive _≈_ _≈′_
  trans≈≈′ = is-transitive λ p≈q q≈′r →
    transitive-≈′ (convert p≈q) (convert q≈′r)

  trans∼≈ : ∀ {i} → Transitive _∼_ [ i ]_≈_
  trans∼≈ = is-transitive (transitive-≳≈ ∘ convert {a = ℓ})

  trans∼′≈ : ∀ {i} → Transitive _∼′_ [ i ]_≈_
  trans∼′≈ = is-transitive (transitive-≳≈ ∘ convert {a = ℓ})

  trans∼′≈′ : ∀ {i} → Transitive _∼′_ [ i ]_≈′_
  trans∼′≈′ {i} = is-transitive lemma
    where
    lemma : ∀ {p q r} → p ∼′ q → [ i ] q ≈′ r → [ i ] p ≈′ r
    force (lemma p∼′q q≈′r) =
      transitive-≳≈ (convert {a = ℓ} p∼′q) (force q≈′r)

  trans∼≈′ : ∀ {i} → Transitive _∼_ [ i ]_≈′_
  trans∼≈′ {i} = is-transitive lemma
    where
    lemma : ∀ {p q r} → p ∼ q → [ i ] q ≈′ r → [ i ] p ≈′ r
    force (lemma p∼q q≈′r) =
      transitive-≳≈ (convert {a = ℓ} p∼q) (force q≈′r)

  trans≈∼ : ∀ {i} → Transitive′ [ i ]_≈_ _∼_
  trans≈∼ = is-transitive transitive-≈∼

  trans≈∼′ : ∀ {i} → Transitive′ [ i ]_≈_ _∼′_
  trans≈∼′ = is-transitive (λ p≈q q∼′r →
    transitive-≈∼ p≈q (convert {a = ℓ} q∼′r))

  trans≈′∼ : ∀ {i} → Transitive′ [ i ]_≈′_ _∼_
  trans≈′∼ {i} = is-transitive lemma
    where
    lemma : ∀ {p q r} → [ i ] p ≈′ q → q ∼ r → [ i ] p ≈′ r
    force (lemma p≈′q q∼r) = transitive-≈∼ (force p≈′q) q∼r

  trans≈′∼′ : ∀ {i} → Transitive′ [ i ]_≈′_ _∼′_
  trans≈′∼′ {i} = is-transitive lemma
    where
    lemma : ∀ {p q r} → [ i ] p ≈′ q → q ∼′ r → [ i ] p ≈′ r
    force (lemma p≈′q q∼r) =
      transitive-≈∼ (force p≈′q) (convert {a = ℓ} q∼r)

  trans≳≈ : ∀ {i} → Transitive _≳_ [ i ]_≈_
  trans≳≈ = is-transitive transitive-≳≈

  trans≳′≈ : ∀ {i} → Transitive _≳′_ [ i ]_≈_
  trans≳′≈ = is-transitive (transitive-≳≈ ∘ convert {a = ℓ})

  trans≳′≈′ : ∀ {i} → Transitive _≳′_ [ i ]_≈′_
  trans≳′≈′ {i} = is-transitive lemma
    where
    lemma : ∀ {p q r} → p ≳′ q → [ i ] q ≈′ r → [ i ] p ≈′ r
    force (lemma p≳′q q≈′r) =
      transitive-≳≈ (convert {a = ℓ} p≳′q) (force q≈′r)

  trans≳≈′ : ∀ {i} → Transitive _≳_ [ i ]_≈′_
  trans≳≈′ {i} = is-transitive lemma
    where
    lemma : ∀ {p q r} → p ≳ q → [ i ] q ≈′ r → [ i ] p ≈′ r
    force (lemma p≳q q≈′r) = transitive-≳≈ p≳q (force q≈′r)

  -- For a proof showing that the following lemma cannot, in general,
  -- be made size-preserving in its first argument, see
  -- Bisimilarity.Weak.Delay-monad.size-preserving-transitivity-≈≳ˡ⇔uninhabited.

  trans≈≳ : Transitive′ _≈_ _≳_
  trans≈≳ = is-transitive (λ p≈q → transitive p≈q ∘ ≳⇒≈)

  trans≈≳′ : Transitive′ _≈_ _≳′_
  trans≈≳′ = is-transitive (λ p≈q → transitive p≈q ∘ ≳⇒≈ ∘ convert)

  trans≈′≳′ : Transitive′ _≈′_ _≳′_
  trans≈′≳′ = is-transitive (λ p≈′q → transitive p≈′q ∘ ≳⇒≈′)

  trans≈′≳ : Transitive′ _≈′_ _≳_
  trans≈′≳ = is-transitive (λ p≈′q → transitive p≈′q ∘ ≳⇒≈′ ∘ convert)

  trans≈≲ : ∀ {i} → Transitive′ [ i ]_≈_ _≲_
  trans≈≲ = is-transitive transitive-≈≲

  trans≈≲′ : ∀ {i} → Transitive′ [ i ]_≈_ _≲′_
  trans≈≲′ = is-transitive (λ p≈q q≲r → transitive-≈≲ p≈q (force q≲r))

  trans≈′≲ : ∀ {i} → Transitive′ [ i ]_≈′_ _≲_
  trans≈′≲ {i} = is-transitive lemma
    where
    lemma : ∀ {p q r} → [ i ] p ≈′ q → q ≲ r → [ i ] p ≈′ r
    force (lemma p≈′q q≳′r) =
      transitive-≈≲ (force p≈′q) q≳′r

  trans≈′≲′ : ∀ {i} → Transitive′ [ i ]_≈′_ _≲′_
  trans≈′≲′ = is-transitive (λ p≈′q q≲′r →
                transitive′ p≈′q (force q≲′r))
