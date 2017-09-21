------------------------------------------------------------------------
-- A parametrised coinductive definition that can be used to define
-- strong and weak bisimilarity as well as expansion
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

open import Labelled-transition-system

module Bisimilarity.Coinductive.General
         (lts : LTS)
         (open LTS lts)
         (_[_]↝₁_ _[_]↝₂_ : Proc → Label → Proc → Set)
         (⟶→↝₁ : ∀ {p μ q} → p [ μ ]⟶ q → p [ μ ]↝₁ q)
         (⟶→↝₂ : ∀ {p μ q} → p [ μ ]⟶ q → p [ μ ]↝₂ q)
         where

open import Equality.Propositional as Eq hiding (Extensionality)
open import Logical-equivalence using (_⇔_)
open import Prelude

open import Bijection equality-with-J as Bijection using (_↔_)
open import Function-universe equality-with-J hiding (id; _∘_)
open import H-level equality-with-J
open import H-level.Closure equality-with-J

open import Bisimilarity.Step lts _[_]↝₁_ _[_]↝₂_ as Step public
  using (S̲t̲e̲p̲)
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

Bisimilarity : Size → Rel₂ (# 0) Proc
Bisimilarity i = ν S̲t̲e̲p̲ i

Bisimilarity′ : Size → Rel₂ (# 0) Proc
Bisimilarity′ i = ν′ S̲t̲e̲p̲ i

[_]_∼_ : Size → Proc → Proc → Set
[_]_∼_ = curry ∘ Bisimilarity

[_]_∼′_ : Size → Proc → Proc → Set
[_]_∼′_ = curry ∘ Bisimilarity′

_∼_ : Proc → Proc → Set
_∼_ = [ ∞ ]_∼_

_∼′_ : Proc → Proc → Set
_∼′_ = [ ∞ ]_∼′_

-- Bisimilarity is reflexive.

mutual

  reflexive-∼ : ∀ {p i} → [ i ] p ∼ p
  reflexive-∼ =
    S̲t̲e̲p̲.⟨ (λ p⟶p′ → _ , ⟶→↝₁ p⟶p′ , reflexive-∼′)
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

[_]_≡_ : ∀ {p q} → Size → (_ _ : ν S̲t̲e̲p̲ ∞ (p , q)) → Set
[_]_≡_ = curry ∘ ν-bisimilar

[_]_≡′_ : ∀ {p q} → Size → (_ _ : ν′ S̲t̲e̲p̲ ∞ (p , q)) → Set
[_]_≡′_ = curry ∘ ν′-bisimilar

-- An alternative characterisation of bisimilarity of bisimilarity
-- proofs.

[]≡↔ :
  Eq.Extensionality lzero lzero →
  ∀ {p q} {i : Size} (p∼q₁ p∼q₂ : ν S̲t̲e̲p̲ ∞ (p , q)) →

  [ i ] p∼q₁ ≡ p∼q₂

    ↔

  (∀ {p′ μ} (p⟶p′ : p [ μ ]⟶ p′) →
   let q′₁ , q⟶q′₁ , p′∼q′₁ = S̲t̲e̲p̲.left-to-right p∼q₁ p⟶p′
       q′₂ , q⟶q′₂ , p′∼q′₂ = S̲t̲e̲p̲.left-to-right p∼q₂ p⟶p′
   in ∃ λ (q′₁≡q′₂ : q′₁ ≡ q′₂) →
        subst (q [ μ ]↝₁_) q′₁≡q′₂ q⟶q′₁ ≡ q⟶q′₂
          ×
        [ i ] subst (ν′ S̲t̲e̲p̲ ∞ ∘ (p′ ,_)) q′₁≡q′₂ p′∼q′₁ ≡′ p′∼q′₂)
    ×
  (∀ {q′ μ} (q⟶q′ : q [ μ ]⟶ q′) →
   let p′₁ , p⟶p′₁ , p′∼q′₁ = S̲t̲e̲p̲.right-to-left p∼q₁ q⟶q′
       p′₂ , p⟶p′₂ , p′∼q′₂ = S̲t̲e̲p̲.right-to-left p∼q₂ q⟶q′
   in ∃ λ (p′₁≡p′₂ : p′₁ ≡ p′₂) →
        subst (p [ μ ]↝₂_) p′₁≡p′₂ p⟶p′₁ ≡ p⟶p′₂
          ×
        [ i ] subst (ν′ S̲t̲e̲p̲ ∞ ∘ (_, q′)) p′₁≡p′₂ p′∼q′₁ ≡′ p′∼q′₂)

[]≡↔ ext {p} {q} {i} p∼q₁@(s₁ , f₁) p∼q₂@(s₂ , f₂) =

  [ i ] p∼q₁ ≡ p∼q₂                                                     ↝⟨ ν-bisimilar↔ ext p∼q₁ p∼q₂ ⟩

  ⟦ S̲t̲e̲p̲₁ ⟷ S̲t̲e̲p̲₂ ⟧₂ (ν′-bisimilar i) (p∼q₁ , p∼q₂)                     ↝⟨ ⟦⟷⟧₂↔ ext S̲t̲e̲p̲₁ S̲t̲e̲p̲₂ (ν′-bisimilar i) p∼q₁ p∼q₂ ⟩

  ⟦ S̲t̲e̲p̲₁ ⟧₂ (ν′-bisimilar i)
    ((proj₁ s₁ , f₁ ∘ inj₁) , (proj₁ s₂ , f₂ ∘ inj₁))
    ×
  ⟦ S̲t̲e̲p̲₂ ⟧₂ (ν′-bisimilar i)
    ( (proj₂ s₁ , λ p → f₁ (inj₂ (_ , refl , p)))
    , (proj₂ s₂ , λ p → f₂ (inj₂ (_ , refl , p)))
    )                                                                   ↝⟨ Step₁.⟦S̲t̲e̲p̲⟧₂↔ ext (ν′-bisimilar i) (proj₁ s₁ , f₁ ∘ inj₁)
                                                                                                               (proj₁ s₂ , f₂ ∘ inj₁)
                                                                             ×-cong
                                                                           Step₂.⟦S̲t̲e̲p̲⟧₂↔ ext (ν′-bisimilar i)
                                                                             (proj₂ s₁ , λ p → f₁ (inj₂ (_ , refl , p)))
                                                                             (proj₂ s₂ , λ p → f₂ (inj₂ (_ , refl , p))) ⟩
  (∀ {p′ μ} (p⟶p′ : p [ μ ]⟶ p′) →
   let q′₁ , q⟶q′₁ , p′∼q′₁ =
         Step₁.S̲t̲e̲p̲.challenge (proj₁ s₁ , f₁ ∘ inj₁) p⟶p′
       q′₂ , q⟶q′₂ , p′∼q′₂ =
         Step₁.S̲t̲e̲p̲.challenge (proj₁ s₂ , f₂ ∘ inj₁) p⟶p′
   in ∃ λ (q′₁≡q′₂ : q′₁ ≡ q′₂) →
        subst (q [ μ ]↝₁_) q′₁≡q′₂ q⟶q′₁ ≡ q⟶q′₂
          ×
        [ i ] subst (ν′ S̲t̲e̲p̲ ∞ ∘ (p′ ,_)) q′₁≡q′₂ p′∼q′₁ ≡′ p′∼q′₂)
    ×
  ((∀ {q′ μ} (q⟶q′ : q [ μ ]⟶ q′) →
   let p′₁ , p⟶p′₁ , p′∼q′₁ =
          Step₂.S̲t̲e̲p̲.challenge
             (proj₂ s₁ , λ p → f₁ (inj₂ (_ , refl , p))) q⟶q′
       p′₂ , p⟶p′₂ , p′∼q′₂ =
          Step₂.S̲t̲e̲p̲.challenge
             (proj₂ s₂ , λ p → f₂ (inj₂ (_ , refl , p))) q⟶q′
   in ∃ λ (p′₁≡p′₂ : p′₁ ≡ p′₂) →
        subst (p [ μ ]↝₂_) p′₁≡p′₂ p⟶p′₁ ≡ p⟶p′₂
          ×
        [ i ] subst (ν′ S̲t̲e̲p̲ ∞ ∘ (_, q′)) p′₁≡p′₂ p′∼q′₁ ≡′ p′∼q′₂))    ↔⟨⟩

  (∀ {p′ μ} (p⟶p′ : p [ μ ]⟶ p′) →
   let q′₁ , q⟶q′₁ , p′∼q′₁ = S̲t̲e̲p̲.left-to-right p∼q₁ p⟶p′
       q′₂ , q⟶q′₂ , p′∼q′₂ = S̲t̲e̲p̲.left-to-right p∼q₂ p⟶p′
   in ∃ λ (q′₁≡q′₂ : q′₁ ≡ q′₂) →
        subst (q [ μ ]↝₁_) q′₁≡q′₂ q⟶q′₁ ≡ q⟶q′₂
          ×
        [ i ] subst (ν′ S̲t̲e̲p̲ ∞ ∘ (p′ ,_)) q′₁≡q′₂ p′∼q′₁ ≡′ p′∼q′₂)
    ×
  (∀ {q′ μ} (q⟶q′ : q [ μ ]⟶ q′) →
   let p′₁ , p⟶p′₁ , p′∼q′₁ = S̲t̲e̲p̲.right-to-left p∼q₁ q⟶q′
       p′₂ , p⟶p′₂ , p′∼q′₂ = S̲t̲e̲p̲.right-to-left p∼q₂ q⟶q′
   in ∃ λ (p′₁≡p′₂ : p′₁ ≡ p′₂) →
        subst (p [ μ ]↝₂_) p′₁≡p′₂ p⟶p′₁ ≡ p⟶p′₂
          ×
        [ i ] subst (ν′ S̲t̲e̲p̲ ∞ ∘ (_, q′)) p′₁≡p′₂ p′∼q′₁ ≡′ p′∼q′₂)     □

  where
  open Container

  S̲t̲e̲p̲₁ = Step₁.S̲t̲e̲p̲
  S̲t̲e̲p̲₂ = Step₂.S̲t̲e̲p̲

module Bisimilarity-of-∼
         (ext : Eq.Extensionality lzero lzero)
         {p q} {i : Size}
         (p∼q₁ p∼q₂ : ν S̲t̲e̲p̲ ∞ (p , q))
         where

  -- A "constructor".

  ⟨_,_,_,_,_⟩ :
    (∀ {p′ μ} (p⟶p′ : p [ μ ]⟶ p′) →
     let q′₁ , q⟶q′₁ , p′∼q′₁ = S̲t̲e̲p̲.left-to-right p∼q₁ p⟶p′
         q′₂ , q⟶q′₂ , p′∼q′₂ = S̲t̲e̲p̲.left-to-right p∼q₂ p⟶p′
     in ∃ λ (q′₁≡q′₂ : q′₁ ≡ q′₂) →
          subst (q [ μ ]↝₁_) q′₁≡q′₂ q⟶q′₁ ≡ q⟶q′₂
            ×
          [ i ] subst (ν′ S̲t̲e̲p̲ ∞ ∘ (p′ ,_)) q′₁≡q′₂ p′∼q′₁ ≡′ p′∼q′₂) →
    (∀ {q′ μ} (q⟶q′ : q [ μ ]⟶ q′) →
     let p′₁ , p⟶p′₁ , p′∼q′₁ = S̲t̲e̲p̲.right-to-left p∼q₁ q⟶q′
         p′₂ , p⟶p′₂ , p′∼q′₂ = S̲t̲e̲p̲.right-to-left p∼q₂ q⟶q′
     in ∃ λ (p′₁≡p′₂ : p′₁ ≡ p′₂) →
          subst (p [ μ ]↝₂_) p′₁≡p′₂ p⟶p′₁ ≡ p⟶p′₂
            ×
          [ i ] subst (ν′ S̲t̲e̲p̲ ∞ ∘ (_, q′)) p′₁≡p′₂ p′∼q′₁ ≡′ p′∼q′₂) →
    [ i ] p∼q₁ ≡ p∼q₂
  ⟨_,_,_,_,_⟩ = curry (_↔_.from ([]≡↔ ext p∼q₁ p∼q₂))

  -- Some "projections".

  left-to-right :
    [ i ] p∼q₁ ≡ p∼q₂ →
    ∀ {p′ μ} (p⟶p′ : p [ μ ]⟶ p′) →
    let q′₁ , q⟶q′₁ , p′∼q′₁ = S̲t̲e̲p̲.left-to-right p∼q₁ p⟶p′
        q′₂ , q⟶q′₂ , p′∼q′₂ = S̲t̲e̲p̲.left-to-right p∼q₂ p⟶p′
    in ∃ λ (q′₁≡q′₂ : q′₁ ≡ q′₂) →
         subst (q [ μ ]↝₁_) q′₁≡q′₂ q⟶q′₁ ≡ q⟶q′₂
           ×
         [ i ] subst (ν′ S̲t̲e̲p̲ ∞ ∘ (p′ ,_)) q′₁≡q′₂ p′∼q′₁ ≡′ p′∼q′₂
  left-to-right = proj₁ ∘ _↔_.to ([]≡↔ ext p∼q₁ p∼q₂)

  right-to-left :
    [ i ] p∼q₁ ≡ p∼q₂ →
    ∀ {q′ μ} (q⟶q′ : q [ μ ]⟶ q′) →
    let p′₁ , p⟶p′₁ , p′∼q′₁ = S̲t̲e̲p̲.right-to-left p∼q₁ q⟶q′
        p′₂ , p⟶p′₂ , p′∼q′₂ = S̲t̲e̲p̲.right-to-left p∼q₂ q⟶q′
    in ∃ λ (p′₁≡p′₂ : p′₁ ≡ p′₂) →
         subst (p [ μ ]↝₂_) p′₁≡p′₂ p⟶p′₁ ≡ p⟶p′₂
           ×
         [ i ] subst (ν′ S̲t̲e̲p̲ ∞ ∘ (_, q′)) p′₁≡p′₂ p′∼q′₁ ≡′ p′∼q′₂
  right-to-left = proj₂ ∘ _↔_.to ([]≡↔ ext p∼q₁ p∼q₂)

-- A statement of extensionality for bisimilarity.

Extensionality : Set
Extensionality = ν′-extensionality S̲t̲e̲p̲

-- This form of extensionality can be used to derive another form
-- (in the presence of extensionality for functions).

extensionality :
  Eq.Extensionality lzero lzero →
  Extensionality →
  ∀ {p q} {p∼q₁ p∼q₂ : ν S̲t̲e̲p̲ ∞ (p , q)} →
  [ ∞ ] p∼q₁ ≡ p∼q₂ → p∼q₁ ≡ p∼q₂
extensionality ext ν-ext = ν-extensionality ext ν-ext

open S̲t̲e̲p̲ public using (⟨_,_⟩; left-to-right; right-to-left)
