------------------------------------------------------------------------
-- A coinductive definition of the expansion ordering
------------------------------------------------------------------------

-- The definition of expansion is based on the one in "Enhancements of
-- the bisimulation proof method" by Pous and Sangiorgi.

{-# OPTIONS --without-K #-}

open import Labelled-transition-system

module Expansion {ℓ} (lts : LTS ℓ) where

open import Prelude

import Bisimilarity.Coinductive
import Bisimilarity.Coinductive.Equational-reasoning-instances
import Bisimilarity.Coinductive.General
open import Equational-reasoning
open import Relation

open LTS lts
private
  open module SB = Bisimilarity.Coinductive lts
    using (_∼_; _∼′_; [_]_∼_; [_]_∼′_)

private
  module General =
    Bisimilarity.Coinductive.General lts _[_]⟶̂_ _[_]⇒̂_ ⟶→⟶̂ ⟶→⇒̂

open General public
  using (StepC; ⟨_,_⟩; left-to-right; right-to-left; force;
         [_]_≡_; [_]_≡′_; []≡↔;
         Extensionality; extensionality)
  renaming ( reflexive-∼ to reflexive-≳
           ; reflexive-∼′ to reflexive-≳′
           ; ≡⇒∼ to ≡⇒≳
           ; ∼:_ to ≳:_
           ; ∼′:_ to ≳′:_
           )

-- Some definitions are given in the following way, rather than via
-- open public, to make hyperlinks to these definitions more
-- informative.

Expansion : Size → Rel₂ ℓ Proc
Expansion = General.Bisimilarity

Expansion′ : Size → Rel₂ ℓ Proc
Expansion′ = General.Bisimilarity′

infix 4 _≳_ _≳′_ [_]_≳_ [_]_≳′_

[_]_≳_ : Size → Proc → Proc → Set ℓ
[_]_≳_ = General.[_]_∼_

[_]_≳′_ : Size → Proc → Proc → Set ℓ
[_]_≳′_ = General.[_]_∼′_

_≳_ : Proc → Proc → Set ℓ
_≳_ = General._∼_

_≳′_ : Proc → Proc → Set ℓ
_≳′_ = General._∼′_

-- The converse relation.

infix 4 _≲_ _≲′_ [_]_≲_ [_]_≲′_

[_]_≲_ : Size → Proc → Proc → Set ℓ
[_]_≲_ i = flip [ i ]_≳_

[_]_≲′_ : Size → Proc → Proc → Set ℓ
[_]_≲′_ i = flip [ i ]_≳′_

_≲_ : Proc → Proc → Set ℓ
_≲_ = [ ∞ ]_≲_

_≲′_ : Proc → Proc → Set ℓ
_≲′_ = [ ∞ ]_≲′_

-- Combinators that can perhaps make the code a bit nicer to read.

infix -3 lr-result-⟶̂ rl-result-⇒̂ lr-result-⇒̂ rl-result-⟶̂

lr-result-⟶̂ : ∀ {i p′ q q′} μ → [ i ] p′ ≳′ q′ → q [ μ ]⟶̂ q′ →
              ∃ λ q′ → q [ μ ]⟶̂ q′ × [ i ] p′ ≳′ q′
lr-result-⟶̂ _ p′≳′q′ q⟶̂q′ = _ , q⟶̂q′ , p′≳′q′

rl-result-⇒̂ : ∀ {i p p′ q′} μ → p [ μ ]⇒̂ p′ → [ i ] p′ ≳′ q′ →
              ∃ λ p′ → p [ μ ]⇒̂ p′ × [ i ] p′ ≳′ q′
rl-result-⇒̂ _ p⇒̂p′ p′≳′q′ = _ , p⇒̂p′ , p′≳′q′

lr-result-⇒̂ : ∀ {i p′ q q′} μ → [ i ] p′ ≲′ q′ → q [ μ ]⇒̂ q′ →
              ∃ λ q′ → q [ μ ]⇒̂ q′ × [ i ] p′ ≲′ q′
lr-result-⇒̂ _ p′≲′q′ q⇒̂q′ = _ , q⇒̂q′ , p′≲′q′

rl-result-⟶̂ : ∀ {i p p′ q′} μ → p [ μ ]⟶̂ p′ → [ i ] p′ ≲′ q′ →
              ∃ λ p′ → p [ μ ]⟶̂ p′ × [ i ] p′ ≲′ q′
rl-result-⟶̂ _ p⟶̂p′ p′≲′q′ = _ , p⟶̂p′ , p′≲′q′

syntax lr-result-⟶̂ μ p′≳′q′ q⟶̂q′ = p′≳′q′ ⟵̂[ μ ] q⟶̂q′
syntax rl-result-⇒̂ μ p⇒̂p′ p′≳′q′ = p⇒̂p′ ⇒̂[ μ ] p′≳′q′
syntax lr-result-⇒̂ μ p′≲′q′ q⇒̂q′ = p′≲′q′ ⇐̂[ μ ] q⇒̂q′
syntax rl-result-⟶̂ μ p⟶̂p′ p′≲′q′ = p⟶̂p′ ⟶̂[ μ ] p′≲′q′

-- Strongly bisimilar processes are related by the expansion ordering.

mutual

  ∼⇒≳ : ∀ {i p q} → [ i ] p ∼ q → [ i ] p ≳ q
  ∼⇒≳ {i} = λ p∼q → StepC.⟨ lr p∼q , rl p∼q ⟩
    where
    lr : ∀ {p p′ q μ} →
         [ i ] p ∼ q → p [ μ ]⟶ p′ →
         ∃ λ q′ → q [ μ ]⟶̂ q′ × [ i ] p′ ≳′ q′
    lr p∼q q⟶q′ =
      let p′ , p⟶p′ , p′∼′q′ = SB.left-to-right p∼q q⟶q′
      in p′ , step p⟶p′ , ∼⇒≳′ p′∼′q′

    rl : ∀ {p q q′ μ} →
         [ i ] p ∼ q → q [ μ ]⟶ q′ →
         ∃ λ p′ → p [ μ ]⇒̂ p′ × [ i ] p′ ≳′ q′
    rl p∼q q⟶q′ =
      let p′ , p⟶p′ , p′∼′q′ = SB.right-to-left p∼q q⟶q′
      in p′ , ⟶→⇒̂ p⟶p′ , ∼⇒≳′ p′∼′q′

  ∼⇒≳′ : ∀ {i p q} → [ i ] p ∼′ q → [ i ] p ≳′ q
  force (∼⇒≳′ p∼′q) = ∼⇒≳ (SB.force p∼′q)

-- Expansion is a weak simulation (of a certain kind).

expansion-is-weak :
  ∀ {p p′ q μ} →
  p ≳ q → p [ μ ]⇒̂ p′ →
  ∃ λ q′ → q [ μ ]⇒̂ q′ × p′ ≳ q′
expansion-is-weak =
  is-weak StepC.left-to-right (λ p≳′q → force p≳′q) ⟶̂→⇒ ⟶̂→⇒̂

-- The converse of expansion is a weak simulation (of a certain kind).

converse-of-expansion-is-weak :
  ∀ {p p′ q μ} →
  p ≲ q → p [ μ ]⇒̂ p′ →
  ∃ λ q′ → q [ μ ]⇒̂ q′ × p′ ≲ q′
converse-of-expansion-is-weak =
  is-weak StepC.right-to-left (λ p≲′q → force p≲′q) ⇒̂→⇒ id

mutual

  -- Expansion is transitive.
  --
  -- Note that the transitivity proof is not claimed to be fully
  -- size-preserving. For a proof showing that it cannot, in general,
  -- be size-preserving in the first argument, see
  -- Expansion.Delay-monad.size-preserving-transitivityˡ⇔uninhabited.

  transitive-≳ : ∀ {i p q r} → p ≳ q → [ i ] q ≳ r → [ i ] p ≳ r
  transitive-≳ {i} = λ p≳q q≳r → StepC.⟨ lr p≳q q≳r , rl p≳q q≳r ⟩
    where
    lr : ∀ {p p′ q r μ} →
         p ≳ q → [ i ] q ≳ r → p [ μ ]⟶ p′ →
         ∃ λ r′ → r [ μ ]⟶̂ r′ × [ i ] p′ ≳′ r′
    lr p≳q q≳r p⟶p′ with StepC.left-to-right p≳q p⟶p′
    ... | _  , done s , p′≳′q  =
      _ , done s
        , transitive-≳′ p′≳′q (record { force = λ { {_} → q≳r } })
    ... | q′ , step q⟶q′ , p′≳′q′ =
      let r′ , r⟶̂r′ , q′≳′r′ = StepC.left-to-right q≳r q⟶q′
      in r′ , r⟶̂r′ , transitive-≳′ p′≳′q′ q′≳′r′

    rl : ∀ {p q r r′ μ} →
         p ≳ q → [ i ] q ≳ r → r [ μ ]⟶ r′ →
         ∃ λ p′ → p [ μ ]⇒̂ p′ × [ i ] p′ ≳′ r′
    rl p≳q q≳r r⟶r′ =
      let q′ , q⇒̂q′ , q′≳′r′ = StepC.right-to-left q≳r r⟶r′
          p′ , p⇒̂p′ , p′≳q′  = converse-of-expansion-is-weak p≳q q⇒̂q′
      in p′ , p⇒̂p′ , transitive-≳′ (record { force = p′≳q′ }) q′≳′r′

  transitive-≳′ : ∀ {i p q r} → p ≳′ q → [ i ] q ≳′ r → [ i ] p ≳′ r
  force (transitive-≳′ p≳q q≳r) = transitive-≳ (force p≳q) (force q≳r)

-- The following variant of transitivity is fully size-preserving.

mutual

  transitive-≳∼ : ∀ {i p q r} →
                  [ i ] p ≳ q → [ i ] q ∼ r → [ i ] p ≳ r
  transitive-≳∼ {i} {p} {r = r} p≳q q∼r = StepC.⟨ lr , rl ⟩
    where
    rl : ∀ {r′ μ} → r [ μ ]⟶ r′ →
         ∃ λ p′ → p [ μ ]⇒̂ p′ × [ i ] p′ ≳′ r′
    rl r⟶r′ =
      let q′ , q⟶q′ , q′∼′r′ = SB.right-to-left q∼r r⟶r′
          p′ , p⇒̂p′ , p′≳′q′ = StepC.right-to-left p≳q q⟶q′
      in p′ , p⇒̂p′ , transitive-≳∼′ p′≳′q′ q′∼′r′

    lr : ∀ {p′ μ} → p [ μ ]⟶ p′ →
         ∃ λ r′ → r [ μ ]⟶̂ r′ × [ i ] p′ ≳′ r′
    lr p⟶p′ =
      let q′ , q⟶̂q′ , p′≳′q′ = StepC.left-to-right p≳q p⟶p′
          r′ , r⇒̂r′ , q′∼r′  = lemma q∼r q⟶̂q′
      in r′ , r⇒̂r′ , transitive-≳∼′ p′≳′q′ q′∼r′
      where
      lemma :
        ∀ {i p p′ q μ} →
        [ i ] p ∼ q → p [ μ ]⟶̂ p′ →
        ∃ λ q′ → q [ μ ]⟶̂ q′ × [ i ] p′ ∼′ q′
      lemma p∼q (done s)    = _ , done s
                                , record { force = λ { {_} → p∼q } }
      lemma p∼q (step p⟶p′) =
        let q′ , q⟶q′ , p′∼q′ = SB.left-to-right p∼q p⟶p′
        in q′ , ⟶→⟶̂ q⟶q′ , p′∼q′

  transitive-≳∼′ : ∀ {i p q r} →
                   [ i ] p ≳′ q → [ i ] q ∼′ r → [ i ] p ≳′ r
  force (transitive-≳∼′ p≳′q q∼′r) =
    transitive-≳∼ (force p≳′q) (SB.force q∼′r)

-- The following variant of transitivity is partially size-preserving.
--
-- For a proof showing that it cannot, in general, be size-preserving
-- in the first argument, see
-- Expansion.Delay-monad.size-preserving-transitivity-∼≳ˡ⇔uninhabited.

transitive-∼≳ : ∀ {i p q r} →
                p ∼ q → [ i ] q ≳ r → [ i ] p ≳ r
transitive-∼≳ = transitive-≳ ∘ ∼⇒≳
