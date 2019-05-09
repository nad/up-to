------------------------------------------------------------------------
-- A coinductive definition of (strong) similarity
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe --sized-types #-}

open import Labelled-transition-system

module Similarity {ℓ} (lts : LTS ℓ) where

open import Equality.Propositional
open import Prelude
open import Prelude.Size

open import Bisimilarity lts as SB using ([_]_∼_; [_]_∼′_)
open import Indexed-container hiding (⟨_⟩)
open import Relation
import Similarity.General

open LTS lts

private
  module General = Similarity.General lts _[_]⟶_ id

open General public
  using (module StepC; ⟨_⟩; challenge; force;
         reflexive-≤; reflexive-≤′; ≡⇒≤; ≤:_; ≤′:_;
         [_]_≡_; [_]_≡′_; []≡↔; Extensionality; extensionality)

-- StepC is given in the following way, rather than via open public,
-- to make hyperlinks to it more informative.

StepC : Container (Proc × Proc) (Proc × Proc)
StepC = General.StepC

-- The following definitions are given explicitly, in order to make
-- the code easier to follow.

Similarity : Size → Rel₂ ℓ Proc
Similarity = ν StepC

Similarity′ : Size → Rel₂ ℓ Proc
Similarity′ = ν′ StepC

infix 4 [_]_≤_ [_]_≤′_ _≤_ _≤′_

[_]_≤_ : Size → Proc → Proc → Set ℓ
[ i ] p ≤ q = ν StepC i (p , q)

[_]_≤′_ : Size → Proc → Proc → Set ℓ
[ i ] p ≤′ q = ν′ StepC i (p , q)

_≤_ : Proc → Proc → Set ℓ
_≤_ = [ ∞ ]_≤_

_≤′_ : Proc → Proc → Set ℓ
_≤′_ = [ ∞ ]_≤′_

private

  -- However, these definitions are definitionally equivalent to
  -- corresponding definitions in General.

  indirect-Similarity : Similarity ≡ General.Similarity
  indirect-Similarity = refl

  indirect-Similarity′ : Similarity′ ≡ General.Similarity′
  indirect-Similarity′ = refl

  indirect-[]≤ : [_]_≤_ ≡ General.[_]_≤_
  indirect-[]≤ = refl

  indirect-[]≤′ : [_]_≤′_ ≡ General.[_]_≤′_
  indirect-[]≤′ = refl

  indirect-≤ : _≤_ ≡ General._≤_
  indirect-≤ = refl

  indirect-≤′ : _≤′_ ≡ General._≤′_
  indirect-≤′ = refl

mutual

  -- Bisimilarity is contained in similarity.

  ∼⇒≤ : ∀ {i p q} → [ i ] p ∼ q → [ i ] p ≤ q
  ∼⇒≤ = λ p∼q →
    ⟨ (λ q⟶q′ →
         let p′ , p⟶p′ , p′∼′q′ = SB.left-to-right p∼q q⟶q′
         in p′ , p⟶p′ , ∼⇒≤′ p′∼′q′)
    ⟩

  ∼⇒≤′ : ∀ {i p q} → [ i ] p ∼′ q → [ i ] p ≤′ q
  force (∼⇒≤′ p≳′q) = ∼⇒≤ (SB.force p≳′q)

mutual

  -- Similarity is transitive.

  transitive-≤ : ∀ {i p q r} → [ i ] p ≤ q → [ i ] q ≤ r → [ i ] p ≤ r
  transitive-≤ p≤q q≤r =
    ⟨ (λ p⟶p′ →
         let q′ , q⟶q′ , p′≤q′ = challenge p≤q p⟶p′
             r′ , r⟶r′ , q′≤r′ = challenge q≤r q⟶q′
         in r′ , r⟶r′ , transitive-≤′ p′≤q′ q′≤r′)
    ⟩

  transitive-≤′ :
    ∀ {i p q r} → [ i ] p ≤′ q → [ i ] q ≤′ r → [ i ] p ≤′ r
  force (transitive-≤′ p≤q q≤r) = transitive-≤ (force p≤q) (force q≤r)
