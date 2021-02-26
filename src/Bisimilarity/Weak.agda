------------------------------------------------------------------------
-- A coinductive definition of weak bisimilarity
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe --sized-types #-}

open import Labelled-transition-system

module Bisimilarity.Weak {ℓ} (lts : LTS ℓ) where

open import Equality.Propositional
open import Prelude
open import Prelude.Size

import Function-universe equality-with-J as F

import Bisimilarity
import Bisimilarity.Equational-reasoning-instances
import Bisimilarity.General
open import Equational-reasoning
import Expansion
import Expansion.Equational-reasoning-instances
open import Indexed-container using (Container; ν; ν′)
open import Relation
open import Up-to

open LTS lts
private
  open module SB = Bisimilarity lts
    using (_∼_; _∼′_; [_]_∼_; [_]_∼′_)
  open module E = Expansion lts
    using (_≳_; _≳′_; _≲_; [_]_≳_; [_]_≳′_)

private
  module General = Bisimilarity.General lts _[_]⇒̂_ _[_]⇒̂_ ⟶→⇒̂ ⟶→⇒̂

open General public
  using (module StepC; ⟨_,_⟩; left-to-right; right-to-left; force;
         [_]_≡_; [_]_≡′_; []≡↔; Extensionality; extensionality)
  renaming ( reflexive-∼ to reflexive-≈
           ; reflexive-∼′ to reflexive-≈′
           ; ≡⇒∼ to ≡⇒≈
           ; ∼:_ to ≈:_
           ; ∼′:_ to ≈′:_
           ; module Bisimilarity-of-∼ to Bisimilarity-of-≈
           )

-- StepC is given in the following way, rather than via open public,
-- to make hyperlinks to it more informative.

StepC : Container (Proc × Proc) (Proc × Proc)
StepC = General.StepC

-- The following definitions are given explicitly, to make the code
-- easier to follow for readers of the paper.

Weak-bisimilarity : Size → Rel₂ ℓ Proc
Weak-bisimilarity = ν StepC

Weak-bisimilarity′ : Size → Rel₂ ℓ Proc
Weak-bisimilarity′ = ν′ StepC

infix 4 [_]_≈_ [_]_≈′_ _≈_ _≈′_

[_]_≈_ : Size → Proc → Proc → Type ℓ
[ i ] p ≈ q = ν StepC i (p , q)

[_]_≈′_ : Size → Proc → Proc → Type ℓ
[ i ] p ≈′ q = ν′ StepC i (p , q)

_≈_ : Proc → Proc → Type ℓ
_≈_ = [ ∞ ]_≈_

_≈′_ : Proc → Proc → Type ℓ
_≈′_ = [ ∞ ]_≈′_

private

  -- However, these definitions are definitionally equivalent to
  -- corresponding definitions in General.

  indirect-Weak-bisimilarity :
    Weak-bisimilarity ≡ General.Bisimilarity
  indirect-Weak-bisimilarity = refl

  indirect-Weak-bisimilarity′ :
    Weak-bisimilarity′ ≡ General.Bisimilarity′
  indirect-Weak-bisimilarity′ = refl

  indirect-[]≈ : [_]_≈_ ≡ General.[_]_∼_
  indirect-[]≈ = refl

  indirect-[]≈′ : [_]_≈′_ ≡ General.[_]_∼′_
  indirect-[]≈′ = refl

  indirect-≈ : _≈_ ≡ General._∼_
  indirect-≈ = refl

  indirect-≈′ : _≈′_ ≡ General._∼′_
  indirect-≈′ = refl

-- Combinators that can perhaps make the code a bit nicer to read.

infix -3 lr-result rl-result

lr-result : ∀ {i p′ q q′} μ → [ i ] p′ ≈′ q′ → q [ μ ]⇒̂ q′ →
            ∃ λ q′ → q [ μ ]⇒̂ q′ × [ i ] p′ ≈′ q′
lr-result _ p′≈′q′ q⇒̂q′ = _ , q⇒̂q′ , p′≈′q′

rl-result : ∀ {i p p′ q′} μ → p [ μ ]⇒̂ p′ → [ i ] p′ ≈′ q′ →
            ∃ λ p′ → p [ μ ]⇒̂ p′ × [ i ] p′ ≈′ q′
rl-result _ p⇒̂p′ p′≈′q′ = _ , p⇒̂p′ , p′≈′q′

syntax lr-result μ p′≈′q′ q⇒̂q′ = p′≈′q′ ⇐̂[ μ ] q⇒̂q′
syntax rl-result μ p⇒̂p′ p′≈′q′ = p⇒̂p′ ⇒̂[ μ ] p′≈′q′

-- Processes that are related by the expansion ordering are weakly
-- bisimilar.

mutual

  ≳⇒≈ : ∀ {i p q} → [ i ] p ≳ q → [ i ] p ≈ q
  ≳⇒≈ {i} = λ p≳q → StepC.⟨ lr p≳q , rl p≳q ⟩
    where
    lr : ∀ {p p′ q μ} →
         [ i ] p ≳ q → p [ μ ]⟶ p′ →
         ∃ λ q′ → q [ μ ]⇒̂ q′ × [ i ] p′ ≈′ q′
    lr p≳q q⟶q′ =
      let p′ , p⟶̂p′ , p′≳′q′ = E.left-to-right p≳q q⟶q′
      in p′ , ⟶̂→⇒̂ p⟶̂p′ , ≳⇒≈′ p′≳′q′

    rl : ∀ {p q q′ μ} →
         [ i ] p ≳ q → q [ μ ]⟶ q′ →
         ∃ λ p′ → p [ μ ]⇒̂ p′ × [ i ] p′ ≈′ q′
    rl p≳q q⟶q′ =
      let p′ , p⇒p′ , p′≳′q′ = E.right-to-left p≳q q⟶q′
      in p′ , ⇒→⇒̂ p⇒p′ , ≳⇒≈′ p′≳′q′

  ≳⇒≈′ : ∀ {i p q} → [ i ] p ≳′ q → [ i ] p ≈′ q
  force (≳⇒≈′ p≳′q) = ≳⇒≈ (SB.force p≳′q)

-- Strongly bisimilar processes are weakly bisimilar.

∼⇒≈ : ∀ {i p q} → [ i ] p ∼ q → [ i ] p ≈ q
∼⇒≈ = ≳⇒≈ ∘ convert {a = ℓ}

∼⇒≈′ : ∀ {i p q} → [ i ] p ∼′ q → [ i ] p ≈′ q
∼⇒≈′ = ≳⇒≈′ ∘ convert {a = ℓ}

-- Weak bisimilarity is a weak simulation (of one kind).

weak-is-weak⇒ :
  ∀ {p p′ q} →
  p ≈ q → p ⇒ p′ →
  ∃ λ q′ → q ⇒ q′ × p′ ≈ q′
weak-is-weak⇒ = is-weak⇒ StepC.left-to-right (λ p≈′q → force p≈′q) ⇒̂→⇒

-- Weak bisimilarity is a weak simulation (of another kind).

weak-is-weak⇒̂ :
  ∀ {p p′ q μ} →
  p ≈ q → p [ μ ]⇒̂ p′ →
  ∃ λ q′ → q [ μ ]⇒̂ q′ × p′ ≈ q′
weak-is-weak⇒̂ =
  is-weak⇒̂ StepC.left-to-right (λ p≈′q → force p≈′q) ⇒̂→⇒ id

mutual

  -- Weak bisimilarity is symmetric.

  symmetric-≈ : ∀ {i p q} → [ i ] p ≈ q → [ i ] q ≈ p
  symmetric-≈ p≈q =
    StepC.⟨ Σ-map id (Σ-map id symmetric-≈′) ∘ StepC.right-to-left p≈q
          , Σ-map id (Σ-map id symmetric-≈′) ∘ StepC.left-to-right p≈q
          ⟩

  symmetric-≈′ : ∀ {i p q} → [ i ] p ≈′ q → [ i ] q ≈′ p
  force (symmetric-≈′ p≈q) = symmetric-≈ (force p≈q)

private

  -- An alternative proof of symmetry.

  alternative-proof-of-symmetry : ∀ {i p q} → [ i ] p ≈ q → [ i ] q ≈ p
  alternative-proof-of-symmetry {i} =
    uncurry [ i ]_≈_ ⁻¹  ⊆⟨ ν-symmetric _ _ swap refl F.id ⟩∎
    uncurry [ i ]_≈_     ∎

mutual

  -- Weak bisimilarity is transitive.
  --
  -- Note that the transitivity proof is not claimed to be
  -- size-preserving. For proofs showing that transitivity cannot, in
  -- general, be size-preserving in any of its arguments, see
  -- Bisimilarity.Weak.Delay-monad.size-preserving-transitivityʳ⇔uninhabited
  -- and size-preserving-transitivityˡ⇔uninhabited.

  transitive-≈ : ∀ {i p q r} → p ≈ q → q ≈ r → [ i ] p ≈ r
  transitive-≈ {i} = λ p≈q q≈r →
    StepC.⟨ lr p≈q q≈r
          , Σ-map id (Σ-map id symmetric-≈′) ∘
            lr (symmetric-≈ q≈r) (symmetric-≈ p≈q)
          ⟩
    where
    lr : ∀ {p p′ q r μ} →
         p ≈ q → q ≈ r → p [ μ ]⟶ p′ →
         ∃ λ r′ → r [ μ ]⇒̂ r′ × [ i ] p′ ≈′ r′
    lr p≈q q≈r p⟶p′ =
      let q′ , q⇒̂q′ , p′≈′q′ = StepC.left-to-right p≈q p⟶p′
          r′ , r⇒̂r′ , q′≈r′  = weak-is-weak⇒̂ q≈r q⇒̂q′
      in r′ , r⇒̂r′ , transitive-≈′ p′≈′q′ q′≈r′

  transitive-≈′ : ∀ {i p q r} → p ≈′ q → q ≈ r → [ i ] p ≈′ r
  force (transitive-≈′ p≈q q≈r) = transitive-≈ (force p≈q) q≈r

-- The following variants of transitivity are partially
-- size-preserving.
--
-- For proofs showing that they cannot, in general, be size-preserving
-- in the "other" argument, see the following lemmas in
-- Bisimilarity.Weak.Delay-monad:
-- size-preserving-transitivity-≳≈ˡ⇔uninhabited,
-- size-preserving-transitivity-≈≲ʳ⇔uninhabited and
-- size-preserving-transitivity-≈∼ʳ⇔uninhabited.

mutual

  transitive-≳≈ : ∀ {i p q r} →
                  p ≳ q → [ i ] q ≈ r → [ i ] p ≈ r
  transitive-≳≈ {i} {p} {r = r} p≳q q≈r = StepC.⟨ lr , rl ⟩
    where
    lr : ∀ {p′ μ} → p [ μ ]⟶ p′ →
         ∃ λ r′ → r [ μ ]⇒̂ r′ × [ i ] p′ ≈′ r′
    lr p⟶p′ with E.left-to-right p≳q p⟶p′
    ... | _  , done s , p≳′q′  =
      r , silent s done
        , transitive-≳≈′ p≳′q′ (record { force = λ { {_} → q≈r } })
    ... | q′ , step q⟶q′ , p′≳′q′ =
      let r′ , r⇒̂r′ , q′≈′r′ = StepC.left-to-right q≈r q⟶q′
      in r′ , r⇒̂r′ , transitive-≳≈′ p′≳′q′ q′≈′r′

    rl : ∀ {r′ μ} → r [ μ ]⟶ r′ →
         ∃ λ p′ → p [ μ ]⇒̂ p′ × [ i ] p′ ≈′ r′
    rl r⟶r′ =
      let q′ , q⇒̂q′ , q′≈′r′ = StepC.right-to-left q≈r r⟶r′
          p′ , p⇒̂p′ , p′≳q′  = E.converse-of-expansion-is-weak⇒̂ p≳q q⇒̂q′
      in p′ , p⇒̂p′ , transitive-≳≈′ (record { force = p′≳q′ }) q′≈′r′

  transitive-≳≈′ : ∀ {i p q r} →
                   p ≳′ q → [ i ] q ≈′ r → [ i ] p ≈′ r
  force (transitive-≳≈′ p≳′q q≈′r) =
    transitive-≳≈ (force p≳′q) (force q≈′r)

transitive-≈≲ : ∀ {i p q r} →
                [ i ] p ≈ q → q ≲ r → [ i ] p ≈ r
transitive-≈≲ p≈q q≲r =
  symmetric-≈ (transitive-≳≈ q≲r (symmetric-≈ p≈q))

transitive-≈∼ : ∀ {i p q r} →
                [ i ] p ≈ q → q ∼ r → [ i ] p ≈ r
transitive-≈∼ p≈q q∼r =
  symmetric-≈ $
    transitive-≳≈ (convert {a = ℓ} (symmetric q∼r)) (symmetric-≈ p≈q)
