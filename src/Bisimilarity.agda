------------------------------------------------------------------------
-- A coinductive definition of (strong) bisimilarity
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe --sized-types #-}

open import Labelled-transition-system

module Bisimilarity {ℓ} (lts : LTS ℓ) where

open import Equality.Propositional
open import Prelude

import Function-universe equality-with-J as F

import Bisimilarity.General
open import Indexed-container using (Container; ν; ν′)
open import Relation
open import Up-to

open LTS lts

private
  module General = Bisimilarity.General lts _[_]⟶_ _[_]⟶_ id id

open General public
  using (module StepC; ⟨_,_⟩; left-to-right; right-to-left; force;
         reflexive-∼; reflexive-∼′; ≡⇒∼; ∼:_; ∼′:_;
         [_]_≡_; [_]_≡′_; []≡↔; module Bisimilarity-of-∼;
         Extensionality; extensionality)

-- StepC is given in the following way, rather than via open public,
-- to make hyperlinks to it more informative.

StepC : Container (Proc × Proc) (Proc × Proc)
StepC = General.StepC

-- The following definitions are given explicitly, to make the code
-- easier to follow for readers of the paper.

Bisimilarity : Size → Rel₂ ℓ Proc
Bisimilarity = ν StepC

Bisimilarity′ : Size → Rel₂ ℓ Proc
Bisimilarity′ = ν′ StepC

infix 4 [_]_∼_ [_]_∼′_ _∼_ _∼′_

[_]_∼_ : Size → Proc → Proc → Set ℓ
[ i ] p ∼ q = ν StepC i (p , q)

[_]_∼′_ : Size → Proc → Proc → Set ℓ
[ i ] p ∼′ q = ν′ StepC i (p , q)

_∼_ : Proc → Proc → Set ℓ
_∼_ = [ ∞ ]_∼_

_∼′_ : Proc → Proc → Set ℓ
_∼′_ = [ ∞ ]_∼′_

private

  -- However, these definitions are definitionally equivalent to
  -- corresponding definitions in General.

  indirect-Bisimilarity : Bisimilarity ≡ General.Bisimilarity
  indirect-Bisimilarity = refl

  indirect-Bisimilarity′ : Bisimilarity′ ≡ General.Bisimilarity′
  indirect-Bisimilarity′ = refl

  indirect-[]∼ : [_]_∼_ ≡ General.[_]_∼_
  indirect-[]∼ = refl

  indirect-[]∼′ : [_]_∼′_ ≡ General.[_]_∼′_
  indirect-[]∼′ = refl

  indirect-∼ : _∼_ ≡ General._∼_
  indirect-∼ = refl

  indirect-∼′ : _∼′_ ≡ General._∼′_
  indirect-∼′ = refl

-- Combinators that can perhaps make the code a bit nicer to read.

infix -3 _⟶⟨_⟩ʳˡ_ _[_]⟶⟨_⟩ʳˡ_
         lr-result-with-action lr-result-without-action

_⟶⟨_⟩ʳˡ_ : ∀ {i p′ q′ μ} p → p [ μ ]⟶ p′ → [ i ] p′ ∼′ q′ →
           ∃ λ p′ → p [ μ ]⟶ p′ × [ i ] p′ ∼′ q′
_ ⟶⟨ p⟶p′ ⟩ʳˡ p′∼′q′ = _ , p⟶p′ , p′∼′q′

_[_]⟶⟨_⟩ʳˡ_ : ∀ {i p′ q′} p μ → p [ μ ]⟶ p′ → [ i ] p′ ∼′ q′ →
              ∃ λ p′ → p [ μ ]⟶ p′ × [ i ] p′ ∼′ q′
_ [ _ ]⟶⟨ p⟶p′ ⟩ʳˡ p′∼′q′ = _ ⟶⟨ p⟶p′ ⟩ʳˡ p′∼′q′

lr-result-without-action :
  ∀ {i p′ q′ μ} → [ i ] p′ ∼′ q′ → ∀ q → q [ μ ]⟶ q′ →
  ∃ λ q′ → q [ μ ]⟶ q′ × [ i ] p′ ∼′ q′
lr-result-without-action p′∼′q′ _ q⟶q′ = _ , q⟶q′ , p′∼′q′

lr-result-with-action :
  ∀ {i p′ q′} → [ i ] p′ ∼′ q′ → ∀ μ q → q [ μ ]⟶ q′ →
  ∃ λ q′ → q [ μ ]⟶ q′ × [ i ] p′ ∼′ q′
lr-result-with-action p′∼′q′ _ _ q⟶q′ =
  lr-result-without-action  p′∼′q′ _ q⟶q′

syntax lr-result-without-action p′∼q′   q q⟶q′ = p′∼q′      ⟵⟨ q⟶q′ ⟩ q
syntax lr-result-with-action    p′∼q′ μ q q⟶q′ = p′∼q′ [ μ ]⟵⟨ q⟶q′ ⟩ q

-- Strong bisimilarity is a weak simulation (of a certain kind).

strong-is-weak⇒̂ :
  ∀ {p p′ q μ} →
  p ∼ q → p [ μ ]⇒̂ p′ →
  ∃ λ q′ → q [ μ ]⇒̂ q′ × p′ ∼ q′
strong-is-weak⇒̂ =
  is-weak⇒̂ StepC.left-to-right (λ p∼′q → force p∼′q)
           (λ s tr → step s tr done) ⟶→⇒̂

mutual

  -- Bisimilarity is symmetric.

  symmetric-∼ : ∀ {i p q} → [ i ] p ∼ q → [ i ] q ∼ p
  symmetric-∼ p∼q =
    StepC.⟨ Σ-map id (Σ-map id symmetric-∼′) ∘ StepC.right-to-left p∼q
          , Σ-map id (Σ-map id symmetric-∼′) ∘ StepC.left-to-right p∼q
          ⟩

  symmetric-∼′ : ∀ {i p q} → [ i ] p ∼′ q → [ i ] q ∼′ p
  force (symmetric-∼′ p∼q) = symmetric-∼ (force p∼q)

private

  -- An alternative proof of symmetry.

  alternative-proof-of-symmetry : ∀ {i p q} → [ i ] p ∼ q → [ i ] q ∼ p
  alternative-proof-of-symmetry {i} =
    uncurry [ i ]_∼_ ⁻¹  ⊆⟨ ν-symmetric _ _ swap refl F.id ⟩∎
    uncurry [ i ]_∼_     ∎

-- Strong bisimilarity is transitive.

transitive-∼ : ∀ {i p q r} → [ i ] p ∼ q → [ i ] q ∼ r → [ i ] p ∼ r
transitive-∼ {i} = λ p q →
  StepC.⟨ lr p q
        , Σ-map id (Σ-map id symmetric-∼′) ∘
          lr (symmetric-∼ q) (symmetric-∼ p)
        ⟩
  where
  lr : ∀ {p p′ q r μ} →
       [ i ] p ∼ q → [ i ] q ∼ r → p [ μ ]⟶ p′ →
       ∃ λ r′ → r [ μ ]⟶ r′ × [ i ] p′ ∼′ r′
  lr p q tr =
    let (_ , tr′ , p′) = StepC.left-to-right p tr
        (_ , tr″ , q′) = StepC.left-to-right q tr′
    in  (_ , tr″ , λ { .force → transitive-∼ (force p′) (force q′) })

transitive-∼′ :
  ∀ {i p q r} → [ i ] p ∼′ q → [ i ] q ∼′ r → [ i ] p ∼′ r
force (transitive-∼′ p∼q q∼r) = transitive-∼ (force p∼q) (force q∼r)
