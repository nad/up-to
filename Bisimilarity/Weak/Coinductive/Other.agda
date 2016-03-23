------------------------------------------------------------------------
-- Another coinductive definition of weak bisimilarity
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

open import Labelled-transition-system

module Bisimilarity.Weak.Coinductive.Other (lts : LTS) where

open import Equality.Propositional hiding (reflexive; Extensionality)
open import Prelude

import Bisimilarity.Coinductive
import Bisimilarity.Weak.Coinductive

open LTS lts
private
  open module SB = Bisimilarity.Coinductive lts
    using (_∼_; _∼′_; [_]_∼_; [_]_∼′_)

-- Bisimilarity. Note that this definition is small.

mutual

  infix 4 _≈_ _≈′_ [_]_≈_ [_]_≈′_

  record [_]_≈_ (i : Size) (p q : Proc) : Set where
    inductive
    constructor ⟨_,_⟩
    field
      left-to-right :
        ∀ {p′ μ} →
        p [ μ ]⟶ p′ → ∃ λ q′ → q [ μ ]⇒̂ q′ × [ i ] p′ ≈′ q′
      right-to-left :
        ∀ {q′ μ} →
        q [ μ ]⟶ q′ → ∃ λ p′ → p [ μ ]⇒̂ p′ × [ i ] p′ ≈′ q′

  record [_]_≈′_ (i : Size) (p q : Proc) : Set where
    coinductive
    field
      force : {j : Size< i} → [ j ] p ≈ q

_≈_ : Proc → Proc → Set
p ≈ q = [ ∞ ] p ≈ q

_≈′_ : Proc → Proc → Set
p ≈′ q = [ ∞ ] p ≈′ q

-- Combinators that can perhaps make the code a bit nicer to read.

infix -3 _⇒̂⟨_⟩ʳˡ_ _[_]⇒̂⟨_⟩ʳˡ_
         lr-result-with-action lr-result-without-action

_⇒̂⟨_⟩ʳˡ_ : ∀ {i p′ q′ μ} p → p [ μ ]⇒̂ p′ → [ i ] p′ ≈′ q′ →
           ∃ λ p′ → p [ μ ]⇒̂ p′ × [ i ] p′ ≈′ q′
_ ⇒̂⟨ p⇒̂p′ ⟩ʳˡ p′≈′q′ = _ , p⇒̂p′ , p′≈′q′

_[_]⇒̂⟨_⟩ʳˡ_ : ∀ {i p′ q′} p μ → p [ μ ]⇒̂ p′ → [ i ] p′ ≈′ q′ →
              ∃ λ p′ → p [ μ ]⇒̂ p′ × [ i ] p′ ≈′ q′
_ [ _ ]⇒̂⟨ p⇒̂p′ ⟩ʳˡ p′≈′q′ = _ ⇒̂⟨ p⇒̂p′ ⟩ʳˡ p′≈′q′

lr-result-without-action :
  ∀ {i p′ q′ μ} → [ i ] p′ ≈′ q′ → ∀ q → q [ μ ]⇒̂ q′ →
  ∃ λ q′ → q [ μ ]⇒̂ q′ × [ i ] p′ ≈′ q′
lr-result-without-action p′≈′q′ _ q⇒̂q′ = _ , q⇒̂q′ , p′≈′q′

lr-result-with-action :
  ∀ {i p′ q′} → [ i ] p′ ≈′ q′ → ∀ μ q → q [ μ ]⇒̂ q′ →
  ∃ λ q′ → q [ μ ]⇒̂ q′ × [ i ] p′ ≈′ q′
lr-result-with-action p′≈′q′ _ _ q⇒̂q′ =
  lr-result-without-action  p′≈′q′ _ q⇒̂q′

syntax lr-result-without-action p′≈q′   q q⇒̂q′ = p′≈q′      ⇐̂⟨ q⇒̂q′ ⟩ q
syntax lr-result-with-action    p′≈q′ μ q q⇒̂q′ = p′≈q′ [ μ ]⇐̂⟨ q⇒̂q′ ⟩ q

-- Some "equational" reasoning combinators.

infix -1 finally-≈ finally-≈′ finally-′≈ finally-′≈′

finally-≈ : ∀ {i} p q → [ i ] p ≈ q → [ i ] p ≈ q
finally-≈ _ _ p≈q = p≈q

finally-′≈ : ∀ {i} p q → [ ssuc i ] p ≈′ q → [ i ] p ≈ q
finally-′≈ _ _ p≈′q = [_]_≈′_.force p≈′q

finally-≈′ : ∀ {i} p q → [ i ] p ≈ q → [ i ] p ≈′ q
[_]_≈′_.force (finally-≈′ _ _ p≈q) = p≈q

finally-′≈′ : ∀ {i} p q → [ i ] p ≈′ q → [ i ] p ≈′ q
finally-′≈′ _ _ p≈′q = p≈′q

syntax finally-≈   p q p≈q  = p ≈⟨  p≈q  ⟩∎ q
syntax finally-′≈  p q p≈′q = p ≈′⟨ p≈′q ⟩∎ q
syntax finally-≈′  p q p≈q  = p ≈⟨  p≈q  ⟩′∎ q
syntax finally-′≈′ p q p≈′q = p ≈′⟨ p≈′q ⟩′∎ q

-- Weak bisimilarity is a weak bisimulation (of a certain kind).

weak-is-weak :
  ∀ {p p′ q μ} →
  p ≈ q → p [ μ ]⇒̂ p′ →
  ∃ λ q′ → q [ μ ]⇒̂ q′ × p′ ≈ q′
weak-is-weak =
  is-weak [_]_≈_.left-to-right (λ p≈′q → [_]_≈′_.force p≈′q) ⇒̂→⇒ id

-- Bisimilarity is an equivalence relation.

mutual

  reflexive : ∀ {p i} → [ i ] p ≈ p
  reflexive =
    ⟨ (λ p⟶p′ → _ , ⟶⇒⇒̂ p⟶p′ , reflexive′)
    , (λ q⟶q′ → _ , ⟶⇒⇒̂ q⟶q′ , reflexive′)
    ⟩

  reflexive′ : ∀ {p i} → [ i ] p ≈′ p
  [_]_≈′_.force reflexive′ = reflexive

≡⇒≈ : ∀ {p q} → p ≡ q → p ≈ q
≡⇒≈ refl = reflexive

mutual

  symmetric : ∀ {i p q} → [ i ] p ≈ q → [ i ] q ≈ p
  symmetric ⟨ left-to-right , right-to-left ⟩ =
    ⟨ Σ-map id (Σ-map id symmetric′) ∘ right-to-left
    , Σ-map id (Σ-map id symmetric′) ∘ left-to-right
    ⟩

  symmetric′ : ∀ {i p q} → [ i ] p ≈′ q → [ i ] q ≈′ p
  [_]_≈′_.force (symmetric′ p≈q) = symmetric ([_]_≈′_.force p≈q)

mutual

  -- Note that the transitivity proof is not size-preserving.

  -- TODO: I guess that this proof cannot be size-preserving in any of
  -- its two arguments. Perhaps one of the examples given by Pous and
  -- Sangiorgi can be used as a counterexample.

  transitive : ∀ {i p q r} → p ≈ q → q ≈ r → [ i ] p ≈ r
  transitive {i} = λ p≈q q≈r →
    ⟨ lr p≈q q≈r
    , Σ-map id (Σ-map id symmetric′) ∘
      lr (symmetric q≈r) (symmetric p≈q)
    ⟩
    where
    lr : ∀ {p p′ q r μ} →
         p ≈ q → q ≈ r → p [ μ ]⟶ p′ →
         ∃ λ r′ → r [ μ ]⇒̂ r′ × [ i ] p′ ≈′ r′
    lr p≈q q≈r p⟶p′ =
      let q′ , q⇒̂q′ , p′≈′q′ = [_]_≈_.left-to-right p≈q p⟶p′
          r′ , r⇒̂r′ , q′≈r′  = weak-is-weak q≈r q⇒̂q′
      in r′ , r⇒̂r′ , transitive′ p′≈′q′ q′≈r′

  transitive′ : ∀ {i p q r} → p ≈′ q → q ≈ r → [ i ] p ≈′ r
  [_]_≈′_.force (transitive′ p≈q q≈r) =
    transitive ([_]_≈′_.force p≈q) q≈r

-- The following variants of transitivity are partially
-- size-preserving.

-- TODO: I guess that they cannot be fully size-preserving.

mutual

  ≈∼-transitive : ∀ {i p q r} →
                  [ i ] p ≈ q → q ∼ r → [ i ] p ≈ r
  ≈∼-transitive {i} {p} {r = r} p≈q q∼r = ⟨ lr , rl ⟩
    where
    rl : ∀ {r′ μ} → r [ μ ]⟶ r′ →
         ∃ λ p′ → p [ μ ]⇒̂ p′ × [ i ] p′ ≈′ r′
    rl r⟶r′ =
      let q′ , q⟶q′ , q′∼′r′ = [_]_∼_.right-to-left q∼r r⟶r′
          p′ , p⇒̂p′ , p′≈′q′ = [_]_≈_.right-to-left p≈q q⟶q′
      in p′ , p⇒̂p′ , ≈∼-transitive′ˡʳ p′≈′q′ q′∼′r′

    lr : ∀ {p′ μ} → p [ μ ]⟶ p′ →
         ∃ λ r′ → r [ μ ]⇒̂ r′ × [ i ] p′ ≈′ r′
    lr p⟶p′ =
      let q′ , q⇒̂q′ , p′≈′q′ = [_]_≈_.left-to-right p≈q p⟶p′
          r′ , r⇒̂r′ , q′∼r′  = SB.strong-is-weak q∼r q⇒̂q′
      in r′ , r⇒̂r′ , ≈∼-transitive′ˡʳ p′≈′q′ (_ SB.∼⟨ q′∼r′ ⟩′∎ _)

  ≈∼-transitive′ˡʳ : ∀ {i p q r} →
                     [ i ] p ≈′ q → q ∼′ r → [ i ] p ≈′ r
  [_]_≈′_.force (≈∼-transitive′ˡʳ p≈′q q∼′r) =
    ≈∼-transitive ([_]_≈′_.force p≈′q) ([_]_∼′_.force q∼′r)

∼≈-transitive : ∀ {i p q r} →
                p ∼ q → [ i ] q ≈ r → [ i ] p ≈ r
∼≈-transitive p∼q q≈r =
  symmetric (≈∼-transitive (symmetric q≈r) (SB.symmetric p∼q))

-- Strongly bisimilar processes are weakly bisimilar.

mutual

  ∼⇒≈ : ∀ {i p q} → [ i ] p ∼ q → [ i ] p ≈ q
  ∼⇒≈ {i} = λ p∼q →
    ⟨ Σ-map id (Σ-map id symmetric′) ∘ rl (SB.symmetric p∼q)
    , rl p∼q
    ⟩
    where
    rl : ∀ {p q q′ μ} →
         [ i ] p ∼ q → q [ μ ]⟶ q′ →
         ∃ λ p′ → p [ μ ]⇒̂ p′ × [ i ] p′ ≈′ q′
    rl p∼q q⟶q′ =
      let p′ , p⟶p′ , p′∼′q′ = [_]_∼_.right-to-left p∼q q⟶q′
      in p′ , ⟶⇒⇒̂ p⟶p′ , ∼⇒≈″ p′∼′q′

  ∼⇒≈″ : ∀ {i p q} → [ i ] p ∼′ q → [ i ] p ≈′ q
  [_]_≈′_.force (∼⇒≈″ p∼′q) = ∼⇒≈ ([_]_∼′_.force p∼′q)

∼⇒≈′ : ∀ {i p q} → [ i ] p ∼ q → [ i ] p ≈′ q
[_]_≈′_.force (∼⇒≈′ p∼q) = ∼⇒≈ p∼q

-- More "equational" reasoning combinators.

infix  -1 finally-∼ finally-∼′ finally-′∼ finally-′∼′
infixr -2 _≈⟨_⟩_ _≈′⟨_⟩_ _≈′⟨_⟩′_ _≈⟨_⟩′_
          _∼⟨_⟩_ _∼′⟨_⟩_ _∼′⟨_⟩′_ _∼⟨_⟩′_

_≈⟨_⟩_ : ∀ p {q r} → p ≈ q → q ≈ r → p ≈ r
_ ≈⟨ p≈q ⟩ q≈r = transitive p≈q q≈r

_≈′⟨_⟩_ : ∀ p {q r} → p ≈′ q → q ≈ r → p ≈ r
_ ≈′⟨ p≈′q ⟩ q≈r = transitive ([_]_≈′_.force p≈′q) q≈r

_≈′⟨_⟩′_ : ∀ p {q r} → p ≈′ q → q ≈′ r → p ≈′ r
_ ≈′⟨ p≈′q ⟩′ q≈′r = transitive′ p≈′q (_ ≈′⟨ q≈′r ⟩∎ _)

_≈⟨_⟩′_ : ∀ p {q r} → p ≈ q → q ≈′ r → p ≈′ r
_ ≈⟨ p≈q ⟩′ q≈′r = transitive′ (_ ≈⟨ p≈q ⟩′∎ _) (_ ≈′⟨ q≈′r ⟩∎ _)

_∼⟨_⟩_ : ∀ {i} p {q r} → p ∼ q → [ i ] q ≈ r → [ i ] p ≈ r
_ ∼⟨ p∼q ⟩ q≈r = ∼≈-transitive p∼q q≈r

_∼′⟨_⟩_ : ∀ {i} p {q r} → p ∼′ q → [ i ] q ≈ r → [ i ] p ≈ r
_ ∼′⟨ p∼′q ⟩ q≈r = ∼≈-transitive (_ SB.∼′⟨ p∼′q ⟩∎ _) q≈r

_∼′⟨_⟩′_ : ∀ {i} p {q r} → p ∼′ q → [ i ] q ≈′ r → [ i ] p ≈′ r
[_]_≈′_.force (_ ∼′⟨ p∼′q ⟩′ q≈′r) =
  ∼≈-transitive ([_]_∼′_.force p∼′q) ([_]_≈′_.force q≈′r)

_∼⟨_⟩′_ : ∀ {i} p {q r} → p ∼ q → [ i ] q ≈′ r → [ i ] p ≈′ r
[_]_≈′_.force (_ ∼⟨ p∼q ⟩′ q≈′r) =
  ∼≈-transitive p∼q ([_]_≈′_.force q≈′r)

finally-∼ : ∀ p q → p ∼ q → p ≈ q
finally-∼ _ _ p∼q = ∼⇒≈ p∼q

finally-′∼ : ∀ p q → p ∼′ q → p ≈ q
finally-′∼ _ _ p∼′q = _ ≈′⟨ ∼⇒≈″ p∼′q ⟩∎ _

finally-∼′ : ∀ p q → p ∼ q → p ≈′ q
finally-∼′ _ _ p∼q = ∼⇒≈′ p∼q

finally-′∼′ : ∀ p q → p ∼′ q → p ≈′ q
finally-′∼′ _ _ p∼′q = ∼⇒≈″ p∼′q

syntax finally-∼   p q p∼q  = p ∼⟨  p∼q  ⟩∎ q
syntax finally-′∼  p q p∼′q = p ∼′⟨ p∼′q ⟩∎ q
syntax finally-∼′  p q p∼q  = p ∼⟨  p∼q  ⟩′∎ q
syntax finally-′∼′ p q p∼′q = p ∼′⟨ p∼′q ⟩′∎ q

-- Strong bisimilarity of weak bisimilarity proofs.
--
-- TODO: Define in a less monolithic way?

mutual

  infix 4 [_]_≡_ [_]_≡′_

  record [_]_≡_ (i : Size) {p q : Proc}
                (p≈q₁ p≈q₂ : p ≈ q) : Set where
    inductive
    constructor ⟨_,_⟩
    field
      left-to-right :
        ∀ {p′ μ} (p⟶p′ : p [ μ ]⟶ p′) →
        let q′₁ , q⇒̂q′₁ , p′≈q′₁ = [_]_≈_.left-to-right p≈q₁ p⟶p′
            q′₂ , q⇒̂q′₂ , p′≈q′₂ = [_]_≈_.left-to-right p≈q₂ p⟶p′
        in ∃ λ (q′₁≡q′₂ : q′₁ ≡ q′₂) →
             subst (q [ μ ]⇒̂_) q′₁≡q′₂ q⇒̂q′₁ ≡ q⇒̂q′₂
               ×
             [ i ] subst (p′ ≈_) q′₁≡q′₂ ([_]_≈′_.force p′≈q′₁)
                     ≡′
                   [_]_≈′_.force p′≈q′₂
      right-to-left :
        ∀ {q′ μ} (q⟶q′ : q [ μ ]⟶ q′) →
        let p′₁ , p⇒̂p′₁ , p′≈q′₁ = [_]_≈_.right-to-left p≈q₁ q⟶q′
            p′₂ , p⇒̂p′₂ , p′≈q′₂ = [_]_≈_.right-to-left p≈q₂ q⟶q′
        in ∃ λ (p′₁≡p′₂ : p′₁ ≡ p′₂) →
             subst (p [ μ ]⇒̂_) p′₁≡p′₂ p⇒̂p′₁ ≡ p⇒̂p′₂
               ×
             [ i ] subst (_≈ q′) p′₁≡p′₂ ([_]_≈′_.force p′≈q′₁)
                     ≡′
                   [_]_≈′_.force p′≈q′₂

  record [_]_≡′_ (i : Size) {p q : Proc}
                 (p≈q₁ p≈q₂ : p ≈ q) : Set where
    coinductive
    field
      force : {j : Size< i} → [ j ] p≈q₁ ≡ p≈q₂

-- A statement of extensionality for weak bisimilarity.

Extensionality : Set
Extensionality =
  ∀ {p q} {p≈q₁ p≈q₂ : p ≈ q} →
  [ ∞ ] p≈q₁ ≡ p≈q₂ → p≈q₁ ≡ p≈q₂