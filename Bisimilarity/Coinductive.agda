------------------------------------------------------------------------
-- A coinductive definition of (strong) bisimilarity
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

open import Labelled-transition-system

module Bisimilarity.Coinductive (lts : LTS) where

open import Equality.Propositional hiding (reflexive; Extensionality)
open import Prelude

open LTS lts

-- Bisimilarity. Note that this definition is small.

mutual

  infix 4 _∼_ _∼′_ [_]_∼_ [_]_∼′_

  record [_]_∼_ (i : Size) (p q : Proc) : Set where
    inductive
    constructor ⟨_,_⟩
    field
      left-to-right :
        ∀ {p′ μ} →
        p [ μ ]⟶ p′ → ∃ λ q′ → q [ μ ]⟶ q′ × [ i ] p′ ∼′ q′
      right-to-left :
        ∀ {q′ μ} →
        q [ μ ]⟶ q′ → ∃ λ p′ → p [ μ ]⟶ p′ × [ i ] p′ ∼′ q′

  record [_]_∼′_ (i : Size) (p q : Proc) : Set where
    coinductive
    field
      force : {j : Size< i} → [ j ] p ∼ q

_∼_ : Proc → Proc → Set
p ∼ q = [ ∞ ] p ∼ q

_∼′_ : Proc → Proc → Set
p ∼′ q = [ ∞ ] p ∼′ q

-- Bisimilarity is an equivalence relation.

mutual

  reflexive : ∀ {p i} → [ i ] p ∼ p
  reflexive =
    ⟨ (λ p⟶p′ → _ , p⟶p′ , reflexive′)
    , (λ q⟶q′ → _ , q⟶q′ , reflexive′)
    ⟩

  reflexive′ : ∀ {p i} → [ i ] p ∼′ p
  [_]_∼′_.force reflexive′ = reflexive

≡⇒∼ : ∀ {p q} → p ≡ q → p ∼ q
≡⇒∼ refl = reflexive

mutual

  symmetric : ∀ {i p q} → [ i ] p ∼ q → [ i ] q ∼ p
  symmetric ⟨ left-to-right , right-to-left ⟩ =
    ⟨ Σ-map id (Σ-map id symmetric′) ∘ right-to-left
    , Σ-map id (Σ-map id symmetric′) ∘ left-to-right
    ⟩

  symmetric′ : ∀ {i p q} → [ i ] p ∼′ q → [ i ] q ∼′ p
  [_]_∼′_.force (symmetric′ p∼q) = symmetric ([_]_∼′_.force p∼q)

mutual

  transitive : ∀ {i p q r} → [ i ] p ∼ q → [ i ] q ∼ r → [ i ] p ∼ r
  transitive ⟨ left-to-right₁ , right-to-left₁ ⟩
             ⟨ left-to-right₂ , right-to-left₂ ⟩ =
    ⟨ (λ p⟶p′ → let q′ , q⟶q′ , p′∼q′ = left-to-right₁ p⟶p′
                    r′ , r⟶r′ , q′∼r′ = left-to-right₂ q⟶q′
                in r′ , r⟶r′ , transitive′ p′∼q′ q′∼r′)
    , (λ r⟶r′ → let q′ , q⟶q′ , q′∼r′ = right-to-left₂ r⟶r′
                    p′ , p⟶p′ , p′∼q′ = right-to-left₁ q⟶q′
                in p′ , p⟶p′ , transitive′ p′∼q′ q′∼r′)
    ⟩

  transitive′ :
    ∀ {i p q r} → [ i ] p ∼′ q → [ i ] q ∼′ r → [ i ] p ∼′ r
  [_]_∼′_.force (transitive′ p∼q q∼r) =
    transitive ([_]_∼′_.force p∼q) ([_]_∼′_.force q∼r)

-- "Equational" reasoning combinators.

infix  -1 finally-∼ finally-∼′ finally-′∼ finally-′∼′
infixr -2 _∼⟨_⟩_ _∼′⟨_⟩_ _∼′⟨_⟩′_ _∼⟨_⟩′_

_∼⟨_⟩_ : ∀ {i} p {q r} → [ i ] p ∼ q → [ i ] q ∼ r → [ i ] p ∼ r
_ ∼⟨ p∼q ⟩ q∼r = transitive p∼q q∼r

_∼′⟨_⟩_ : ∀ {i} p {q r} → [ ssuc i ] p ∼′ q → [ i ] q ∼ r → [ i ] p ∼ r
_ ∼′⟨ p∼′q ⟩ q∼r = transitive ([_]_∼′_.force p∼′q) q∼r

_∼′⟨_⟩′_ : ∀ {i} p {q r} → [ i ] p ∼′ q → [ i ] q ∼′ r → [ i ] p ∼′ r
_ ∼′⟨ p∼′q ⟩′ q∼′r = transitive′ p∼′q q∼′r

_∼⟨_⟩′_ : ∀ {i} p {q r} → [ i ] p ∼ q → [ i ] q ∼′ r → [ i ] p ∼′ r
[_]_∼′_.force (_ ∼⟨ p∼q ⟩′ q∼′r) = transitive p∼q ([_]_∼′_.force q∼′r)

finally-∼ : ∀ {i} p q → [ i ] p ∼ q → [ i ] p ∼ q
finally-∼ _ _ p∼q = p∼q

finally-′∼ : ∀ {i} p q → [ ssuc i ] p ∼′ q → [ i ] p ∼ q
finally-′∼ _ _ p∼′q = [_]_∼′_.force p∼′q

finally-∼′ : ∀ {i} p q → [ i ] p ∼ q → [ i ] p ∼′ q
[_]_∼′_.force (finally-∼′ _ _ p∼q) = p∼q

finally-′∼′ : ∀ {i} p q → [ i ] p ∼′ q → [ i ] p ∼′ q
finally-′∼′ _ _ p∼′q = p∼′q

syntax finally-∼   p q p∼q  = p ∼⟨  p∼q  ⟩∎ q ∎
syntax finally-′∼  p q p∼′q = p ∼′⟨ p∼′q ⟩∎ q ∎
syntax finally-∼′  p q p∼q  = p ∼⟨  p∼q  ⟩′∎ q ∎
syntax finally-′∼′ p q p∼′q = p ∼′⟨ p∼′q ⟩′∎ q ∎

-- Bisimilarity of bisimilarity proofs.
--
-- TODO: Define in a less monolithic way?

mutual

  infix 4 [_]_≡_ [_]_≡′_

  record [_]_≡_ (i : Size) {p q : Proc}
                (p∼q₁ p∼q₂ : p ∼ q) : Set where
    inductive
    constructor ⟨_,_⟩
    field
      left-to-right :
        ∀ {p′ μ} (p⟶p′ : p [ μ ]⟶ p′) →
        let q′₁ , q⟶q′₁ , p′∼q′₁ = [_]_∼_.left-to-right p∼q₁ p⟶p′
            q′₂ , q⟶q′₂ , p′∼q′₂ = [_]_∼_.left-to-right p∼q₂ p⟶p′
        in ∃ λ (q′₁≡q′₂ : q′₁ ≡ q′₂) →
             subst (q [ μ ]⟶_) q′₁≡q′₂ q⟶q′₁ ≡ q⟶q′₂
               ×
             [ i ] subst (p′ ∼_) q′₁≡q′₂ ([_]_∼′_.force p′∼q′₁)
                     ≡′
                   [_]_∼′_.force p′∼q′₂
      right-to-left :
        ∀ {q′ μ} (q⟶q′ : q [ μ ]⟶ q′) →
        let p′₁ , p⟶p′₁ , p′∼q′₁ = [_]_∼_.right-to-left p∼q₁ q⟶q′
            p′₂ , p⟶p′₂ , p′∼q′₂ = [_]_∼_.right-to-left p∼q₂ q⟶q′
        in ∃ λ (p′₁≡p′₂ : p′₁ ≡ p′₂) →
             subst (p [ μ ]⟶_) p′₁≡p′₂ p⟶p′₁ ≡ p⟶p′₂
               ×
             [ i ] subst (_∼ q′) p′₁≡p′₂ ([_]_∼′_.force p′∼q′₁)
                     ≡′
                   [_]_∼′_.force p′∼q′₂

  record [_]_≡′_ (i : Size) {p q : Proc}
                 (p∼q₁ p∼q₂ : p ∼ q) : Set where
    coinductive
    field
      force : {j : Size< i} → [ j ] p∼q₁ ≡ p∼q₂

-- A statement of extensionality for bisimilarity.

Extensionality : Set
Extensionality =
  ∀ {p q} {p∼q₁ p∼q₂ : p ∼ q} →
  [ ∞ ] p∼q₁ ≡ p∼q₂ → p∼q₁ ≡ p∼q₂
