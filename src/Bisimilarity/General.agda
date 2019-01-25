------------------------------------------------------------------------
-- A parametrised coinductive definition that can be used to define
-- strong and weak bisimilarity as well as expansion
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe --sized-types #-}

open import Labelled-transition-system

module Bisimilarity.General
         {ℓ}
         (lts : LTS ℓ)
         (open LTS lts)
         (_[_]↝₁_ _[_]↝₂_ : Proc → Label → Proc → Set ℓ)
         (⟶→↝₁ : ∀ {p μ q} → p [ μ ]⟶ q → p [ μ ]↝₁ q)
         (⟶→↝₂ : ∀ {p μ q} → p [ μ ]⟶ q → p [ μ ]↝₂ q)
         where

open import Equality.Propositional as Eq hiding (Extensionality)
open import Logical-equivalence using (_⇔_)
open import Prelude
open import Size

open import Bijection equality-with-J as Bijection using (_↔_)
open import Function-universe equality-with-J hiding (id; _∘_)
open import H-level equality-with-J
open import H-level.Closure equality-with-J

open import Bisimilarity.Step lts _[_]↝₁_ _[_]↝₂_ as Step public
  using (StepC)
open import Indexed-container hiding (⟨_⟩; Bisimilarity)
open import Indexed-container.Combinators hiding (id; _∘_)
open import Relation
import Similarity.Step lts _[_]↝₁_ as Step₁
import Similarity.Step lts _[_]↝₂_ as Step₂

open Indexed-container public using (force)

------------------------------------------------------------------------
-- Bisimilarity

-- Bisimilarity. Note that this definition is small.

infix 4 _∼_ _∼′_ [_]_∼_ [_]_∼′_

Bisimilarity : Size → Rel₂ ℓ Proc
Bisimilarity = ν StepC

Bisimilarity′ : Size → Rel₂ ℓ Proc
Bisimilarity′ = ν′ StepC

[_]_∼_ : Size → Proc → Proc → Set ℓ
[_]_∼_ = curry ∘ Bisimilarity

[_]_∼′_ : Size → Proc → Proc → Set ℓ
[_]_∼′_ = curry ∘ Bisimilarity′

_∼_ : Proc → Proc → Set ℓ
_∼_ = [ ∞ ]_∼_

_∼′_ : Proc → Proc → Set ℓ
_∼′_ = [ ∞ ]_∼′_

-- Bisimilarity is reflexive.

mutual

  reflexive-∼ : ∀ {p i} → [ i ] p ∼ p
  reflexive-∼ =
    StepC.⟨ (λ p⟶p′ → _ , ⟶→↝₁ p⟶p′ , reflexive-∼′)
          , (λ q⟶q′ → _ , ⟶→↝₂ q⟶q′ , reflexive-∼′)
          ⟩

  reflexive-∼′ : ∀ {p i} → [ i ] p ∼′ p
  force reflexive-∼′ = reflexive-∼

≡⇒∼ : ∀ {p q} → p ≡ q → p ∼ q
≡⇒∼ refl = reflexive-∼

-- Functions that can be used to aid the instance resolution
-- mechanism.

infix -2 ∼:_ ∼′:_

∼:_ : ∀ {i p q} → [ i ] p ∼ q → [ i ] p ∼ q
∼:_ = id

∼′:_ : ∀ {i p q} → [ i ] p ∼′ q → [ i ] p ∼′ q
∼′:_ = id

------------------------------------------------------------------------
-- Bisimilarity for bisimilarity

-- Bisimilarity of bisimilarity proofs.

infix 4 [_]_≡_ [_]_≡′_

[_]_≡_ : ∀ {p q} → Size → (_ _ : ν StepC ∞ (p , q)) → Set ℓ
[_]_≡_ = curry ∘ ν-bisimilar

[_]_≡′_ : ∀ {p q} → Size → (_ _ : ν′ StepC ∞ (p , q)) → Set ℓ
[_]_≡′_ = curry ∘ ν′-bisimilar

-- An alternative characterisation of bisimilarity of bisimilarity
-- proofs.

[]≡↔ :
  Eq.Extensionality ℓ ℓ →
  ∀ {p q} {i : Size} (p∼q₁ p∼q₂ : ν StepC ∞ (p , q)) →

  [ i ] p∼q₁ ≡ p∼q₂

    ↔

  (∀ {p′ μ} (p⟶p′ : p [ μ ]⟶ p′) →
   let q′₁ , q⟶q′₁ , p′∼q′₁ = StepC.left-to-right p∼q₁ p⟶p′
       q′₂ , q⟶q′₂ , p′∼q′₂ = StepC.left-to-right p∼q₂ p⟶p′
   in ∃ λ (q′₁≡q′₂ : q′₁ ≡ q′₂) →
        subst (q [ μ ]↝₁_) q′₁≡q′₂ q⟶q′₁ ≡ q⟶q′₂
          ×
        [ i ] subst (ν′ StepC ∞ ∘ (p′ ,_)) q′₁≡q′₂ p′∼q′₁ ≡′ p′∼q′₂)
    ×
  (∀ {q′ μ} (q⟶q′ : q [ μ ]⟶ q′) →
   let p′₁ , p⟶p′₁ , p′∼q′₁ = StepC.right-to-left p∼q₁ q⟶q′
       p′₂ , p⟶p′₂ , p′∼q′₂ = StepC.right-to-left p∼q₂ q⟶q′
   in ∃ λ (p′₁≡p′₂ : p′₁ ≡ p′₂) →
        subst (p [ μ ]↝₂_) p′₁≡p′₂ p⟶p′₁ ≡ p⟶p′₂
          ×
        [ i ] subst (ν′ StepC ∞ ∘ (_, q′)) p′₁≡p′₂ p′∼q′₁ ≡′ p′∼q′₂)

[]≡↔ ext {p} {q} {i} p∼q₁@(s₁ , f₁) p∼q₂@(s₂ , f₂) =

  [ i ] p∼q₁ ≡ p∼q₂                                                    ↝⟨ ν-bisimilar↔ ext p∼q₁ p∼q₂ ⟩

  ⟦ StepC₁ ⟷ StepC₂ ⟧₂ (ν′-bisimilar i) (p∼q₁ , p∼q₂)                  ↝⟨ ⟦⟷⟧₂↔ ext StepC₁ StepC₂ (ν′-bisimilar i) p∼q₁ p∼q₂ ⟩

  ⟦ StepC₁ ⟧₂ (ν′-bisimilar i)
    ((proj₁ s₁ , f₁ ∘ inj₁) , (proj₁ s₂ , f₂ ∘ inj₁))
    ×
  ⟦ StepC₂ ⟧₂ (ν′-bisimilar i)
    ( (proj₂ s₁ , λ p → f₁ (inj₂ (_ , refl , p)))
    , (proj₂ s₂ , λ p → f₂ (inj₂ (_ , refl , p)))
    )                                                                  ↝⟨ Step₁.⟦StepC⟧₂↔ ext (ν′-bisimilar i) (proj₁ s₁ , f₁ ∘ inj₁)
                                                                                                               (proj₁ s₂ , f₂ ∘ inj₁)
                                                                            ×-cong
                                                                          Step₂.⟦StepC⟧₂↔ ext (ν′-bisimilar i)
                                                                            (proj₂ s₁ , λ p → f₁ (inj₂ (_ , refl , p)))
                                                                            (proj₂ s₂ , λ p → f₂ (inj₂ (_ , refl , p))) ⟩
  (∀ {p′ μ} (p⟶p′ : p [ μ ]⟶ p′) →
   let q′₁ , q⟶q′₁ , p′∼q′₁ =
         Step₁.StepC.challenge (proj₁ s₁ , f₁ ∘ inj₁) p⟶p′
       q′₂ , q⟶q′₂ , p′∼q′₂ =
         Step₁.StepC.challenge (proj₁ s₂ , f₂ ∘ inj₁) p⟶p′
   in ∃ λ (q′₁≡q′₂ : q′₁ ≡ q′₂) →
        subst (q [ μ ]↝₁_) q′₁≡q′₂ q⟶q′₁ ≡ q⟶q′₂
          ×
        [ i ] subst (ν′ StepC ∞ ∘ (p′ ,_)) q′₁≡q′₂ p′∼q′₁ ≡′ p′∼q′₂)
    ×
  ((∀ {q′ μ} (q⟶q′ : q [ μ ]⟶ q′) →
   let p′₁ , p⟶p′₁ , p′∼q′₁ =
          Step₂.StepC.challenge
             (proj₂ s₁ , λ p → f₁ (inj₂ (_ , refl , p))) q⟶q′
       p′₂ , p⟶p′₂ , p′∼q′₂ =
          Step₂.StepC.challenge
             (proj₂ s₂ , λ p → f₂ (inj₂ (_ , refl , p))) q⟶q′
   in ∃ λ (p′₁≡p′₂ : p′₁ ≡ p′₂) →
        subst (p [ μ ]↝₂_) p′₁≡p′₂ p⟶p′₁ ≡ p⟶p′₂
          ×
        [ i ] subst (ν′ StepC ∞ ∘ (_, q′)) p′₁≡p′₂ p′∼q′₁ ≡′ p′∼q′₂))  ↔⟨⟩

  (∀ {p′ μ} (p⟶p′ : p [ μ ]⟶ p′) →
   let q′₁ , q⟶q′₁ , p′∼q′₁ = StepC.left-to-right p∼q₁ p⟶p′
       q′₂ , q⟶q′₂ , p′∼q′₂ = StepC.left-to-right p∼q₂ p⟶p′
   in ∃ λ (q′₁≡q′₂ : q′₁ ≡ q′₂) →
        subst (q [ μ ]↝₁_) q′₁≡q′₂ q⟶q′₁ ≡ q⟶q′₂
          ×
        [ i ] subst (ν′ StepC ∞ ∘ (p′ ,_)) q′₁≡q′₂ p′∼q′₁ ≡′ p′∼q′₂)
    ×
  (∀ {q′ μ} (q⟶q′ : q [ μ ]⟶ q′) →
   let p′₁ , p⟶p′₁ , p′∼q′₁ = StepC.right-to-left p∼q₁ q⟶q′
       p′₂ , p⟶p′₂ , p′∼q′₂ = StepC.right-to-left p∼q₂ q⟶q′
   in ∃ λ (p′₁≡p′₂ : p′₁ ≡ p′₂) →
        subst (p [ μ ]↝₂_) p′₁≡p′₂ p⟶p′₁ ≡ p⟶p′₂
          ×
        [ i ] subst (ν′ StepC ∞ ∘ (_, q′)) p′₁≡p′₂ p′∼q′₁ ≡′ p′∼q′₂)   □

  where
  open Container

  StepC₁ = Step₁.StepC
  StepC₂ = Step₂.StepC

module Bisimilarity-of-∼
         (ext : Eq.Extensionality ℓ ℓ)
         {p q} {i : Size}
         (p∼q₁ p∼q₂ : ν StepC ∞ (p , q))
         where

  -- A "constructor".

  ⟨_,_,_,_,_⟩ :
    (∀ {p′ μ} (p⟶p′ : p [ μ ]⟶ p′) →
     let q′₁ , q⟶q′₁ , p′∼q′₁ = StepC.left-to-right p∼q₁ p⟶p′
         q′₂ , q⟶q′₂ , p′∼q′₂ = StepC.left-to-right p∼q₂ p⟶p′
     in ∃ λ (q′₁≡q′₂ : q′₁ ≡ q′₂) →
          subst (q [ μ ]↝₁_) q′₁≡q′₂ q⟶q′₁ ≡ q⟶q′₂
            ×
          [ i ] subst (ν′ StepC ∞ ∘ (p′ ,_)) q′₁≡q′₂ p′∼q′₁ ≡′ p′∼q′₂) →
    (∀ {q′ μ} (q⟶q′ : q [ μ ]⟶ q′) →
     let p′₁ , p⟶p′₁ , p′∼q′₁ = StepC.right-to-left p∼q₁ q⟶q′
         p′₂ , p⟶p′₂ , p′∼q′₂ = StepC.right-to-left p∼q₂ q⟶q′
     in ∃ λ (p′₁≡p′₂ : p′₁ ≡ p′₂) →
          subst (p [ μ ]↝₂_) p′₁≡p′₂ p⟶p′₁ ≡ p⟶p′₂
            ×
          [ i ] subst (ν′ StepC ∞ ∘ (_, q′)) p′₁≡p′₂ p′∼q′₁ ≡′ p′∼q′₂) →
    [ i ] p∼q₁ ≡ p∼q₂
  ⟨_,_,_,_,_⟩ = curry (_↔_.from ([]≡↔ ext p∼q₁ p∼q₂))

  -- Some "projections".

  left-to-right :
    [ i ] p∼q₁ ≡ p∼q₂ →
    ∀ {p′ μ} (p⟶p′ : p [ μ ]⟶ p′) →
    let q′₁ , q⟶q′₁ , p′∼q′₁ = StepC.left-to-right p∼q₁ p⟶p′
        q′₂ , q⟶q′₂ , p′∼q′₂ = StepC.left-to-right p∼q₂ p⟶p′
    in ∃ λ (q′₁≡q′₂ : q′₁ ≡ q′₂) →
         subst (q [ μ ]↝₁_) q′₁≡q′₂ q⟶q′₁ ≡ q⟶q′₂
           ×
         [ i ] subst (ν′ StepC ∞ ∘ (p′ ,_)) q′₁≡q′₂ p′∼q′₁ ≡′ p′∼q′₂
  left-to-right = proj₁ ∘ _↔_.to ([]≡↔ ext p∼q₁ p∼q₂)

  right-to-left :
    [ i ] p∼q₁ ≡ p∼q₂ →
    ∀ {q′ μ} (q⟶q′ : q [ μ ]⟶ q′) →
    let p′₁ , p⟶p′₁ , p′∼q′₁ = StepC.right-to-left p∼q₁ q⟶q′
        p′₂ , p⟶p′₂ , p′∼q′₂ = StepC.right-to-left p∼q₂ q⟶q′
    in ∃ λ (p′₁≡p′₂ : p′₁ ≡ p′₂) →
         subst (p [ μ ]↝₂_) p′₁≡p′₂ p⟶p′₁ ≡ p⟶p′₂
           ×
         [ i ] subst (ν′ StepC ∞ ∘ (_, q′)) p′₁≡p′₂ p′∼q′₁ ≡′ p′∼q′₂
  right-to-left = proj₂ ∘ _↔_.to ([]≡↔ ext p∼q₁ p∼q₂)

-- A statement of extensionality for bisimilarity.

Extensionality : Set ℓ
Extensionality = ν′-extensionality StepC

-- This form of extensionality can be used to derive another form
-- (in the presence of extensionality for functions).

extensionality :
  Eq.Extensionality ℓ ℓ →
  Extensionality →
  ∀ {p q} {p∼q₁ p∼q₂ : ν StepC ∞ (p , q)} →
  [ ∞ ] p∼q₁ ≡ p∼q₂ → p∼q₁ ≡ p∼q₂
extensionality ext ν-ext = ν-extensionality ext ν-ext

open StepC public using (⟨_,_⟩; left-to-right; right-to-left)
