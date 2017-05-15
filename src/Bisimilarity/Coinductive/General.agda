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

open import Equality.Propositional hiding (Extensionality)
open import Interval using (ext)
open import Logical-equivalence using (_⇔_)
open import Prelude

open import Bijection equality-with-J as Bijection using (_↔_)
import Equivalence equality-with-J as Eq
open import Function-universe equality-with-J as F hiding (id; _∘_)
open import H-level equality-with-J
open import H-level.Closure equality-with-J

open import Bisimilarity.Step lts _[_]↝₁_ _[_]↝₂_ as Step public
  using (S̲t̲e̲p̲)
open import Indexed-container hiding (⟨_⟩; Bisimilarity)
open import Relation

open Indexed-container public using (force)

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

-- Bisimilarity of bisimilarity proofs.

infix 4 [_]_≡_ [_]_≡′_

[_]_≡_ : ∀ {p q} → Size → (_ _ : ν S̲t̲e̲p̲ ∞ (p , q)) → Set
[_]_≡_ = curry ∘ ν-bisimilar

[_]_≡′_ : ∀ {p q} → Size → (_ _ : ν′ S̲t̲e̲p̲ ∞ (p , q)) → Set
[_]_≡′_ = curry ∘ ν′-bisimilar

-- An alternative characterisation of bisimilarity of bisimilarity
-- proofs.

[]≡↔ :
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

[]≡↔ {p} {q} {i} (s₁@(_ , lr₁ , rl₁) , f₁) (s₂@(_ , lr₂ , rl₂) , f₂) =

  [ i ] s₁ , f₁ ≡ s₂ , f₂                                                 ↝⟨ ν-bisimilar↔ (s₁ , f₁) (s₂ , f₂) ⟩

  (∃ λ (eq : s₁ ≡ s₂) →
   ∀ {o} (p : Container.Position S̲t̲e̲p̲ s₁ o) →
   [ i ] f₁ p ≡′ f₂ (subst (λ s → Container.Position S̲t̲e̲p̲ s o) eq p))     ↝⟨ inverse $ Σ-cong ≡×≡↔≡ (λ _ → F.id) ⟩

  (∃ λ (eq : proj₁ s₁ ≡ proj₁ s₂ × proj₂ s₁ ≡ proj₂ s₂) →
   ∀ {o} (p : Container.Position S̲t̲e̲p̲ s₁ o) →
   [ i ] f₁ p ≡′ f₂ (subst (λ s → Container.Position S̲t̲e̲p̲ s o)
                           (cong₂ _,_ (proj₁ eq) (proj₂ eq)) p))          ↝⟨ inverse Σ-assoc ⟩

  (∃ λ (eq₁ : proj₁ s₁ ≡ proj₁ s₂) →
   ∃ λ (eq₂ : proj₂ s₁ ≡ proj₂ s₂) →
   ∀ {o} (p : Container.Position S̲t̲e̲p̲ s₁ o) →
   [ i ] f₁ p ≡′ f₂ (subst (λ s → Container.Position S̲t̲e̲p̲ s o)
                           (cong₂ _,_ eq₁ eq₂) p))                        ↝⟨ drop-⊤-left-Σ (_⇔_.to contractible⇔↔⊤ $
                                                                                            mono₁ 0 (_⇔_.from contractible⇔↔⊤ Step.Magic↔⊤) _ _) ⟩
  (∃ λ (eq : proj₂ s₁ ≡ proj₂ s₂) →
   ∀ {o} (p : Container.Position S̲t̲e̲p̲ s₁ o) →
   [ i ] f₁ p ≡′ f₂ (subst (λ s → Container.Position S̲t̲e̲p̲ s o)
                           (cong₂ _,_ refl eq) p))                        ↝⟨ (∃-cong λ eq → implicit-∀-cong ext $ ∀-cong ext λ _ →
                                                                              ≡⇒↝ _ $
                                                                              cong (λ (eq : s₁ ≡ s₂) →
                                                                                      [ _ ] f₁ _ ≡′
                                                                                            f₂ (subst (λ s → Container.Position S̲t̲e̲p̲ s _) eq _)) $
                                                                              trans-reflˡ (cong (_ ,_) eq)) ⟩
  (∃ λ (eq : proj₂ s₁ ≡ proj₂ s₂) →
   ∀ {o} (p : Container.Position S̲t̲e̲p̲ s₁ o) →
   [ i ] f₁ p ≡′ f₂ (subst (λ s → Container.Position S̲t̲e̲p̲ s o)
                           (cong (_ ,_) eq) p))                           ↝⟨ (∃-cong λ eq → implicit-∀-cong ext $ ∀-cong ext λ _ →
                                                                              ≡⇒↝ _ $ cong (λ p → [ _ ] f₁ _ ≡′ f₂ p) $ sym $
                                                                              subst-∘ _ _ eq) ⟩
  (∃ λ (eq : proj₂ s₁ ≡ proj₂ s₂) →
   ∀ {o} (p : Container.Position S̲t̲e̲p̲ s₁ o) →
   [ i ] f₁ p ≡′ f₂ (subst (λ s → Container.Position S̲t̲e̲p̲ (_ , s) o)
                           eq p))                                         ↝⟨ inverse $ Σ-cong ≡×≡↔≡ (λ _ → F.id) ⟩

  (∃ λ (eq : _≡_ {A = ∀ {p′ μ} → _} lr₁ lr₂
               ×
             _≡_ {A = ∀ {q′ μ} → _} rl₁ rl₂) →
   ∀ {o} (p : Container.Position S̲t̲e̲p̲ s₁ o) →
   [ i ] f₁ p ≡′ f₂ (subst (λ s → Container.Position S̲t̲e̲p̲ (_ , s) o)
                           (cong₂ _,_ (proj₁ eq) (proj₂ eq)) p))          ↝⟨ ∃-cong (λ _ → implicit-∀-cong ext $ Π⊎↔Π×Π ext) ⟩
  (∃ λ (eq : _≡_ {A = ∀ {p′ μ} → _} lr₁ lr₂
               ×
             _≡_ {A = ∀ {q′ μ} → _} rl₁ rl₂) →
   ∀ {p′q′} →
   ((pos : ∃ λ μ → ∃ λ (p⟶p′ : p [ μ ]⟶ proj₁ p′q′) →
           proj₁ (lr₁ p⟶p′) ≡ proj₂ p′q′) →
    [ i ] f₁ (inj₁ pos) ≡′
          f₂ (subst (λ s → Container.Position S̲t̲e̲p̲ (_ , s) p′q′)
                    (cong₂ _,_ (proj₁ eq) (proj₂ eq)) (inj₁ pos)))
     ×
   ((pos : ∃ λ μ → ∃ λ (q⟶q′ : q [ μ ]⟶ proj₂ p′q′) →
           proj₁ (rl₁ q⟶q′) ≡ proj₁ p′q′) →
    [ i ] f₁ (inj₂ pos) ≡′
          f₂ (subst (λ s → Container.Position S̲t̲e̲p̲ (_ , s) p′q′)
                    (cong₂ _,_ (proj₁ eq) (proj₂ eq)) (inj₂ pos))))       ↝⟨ (∃-cong λ eq → implicit-∀-cong ext $
                                                                              (∀-cong ext λ _ → ≡⇒↝ bijection $ lemma₁₁ eq)
                                                                                ×-cong
                                                                              (∀-cong ext λ _ → ≡⇒↝ bijection $ lemma₁₂ eq)) ⟩
  (∃ λ (eq : _≡_ {A = ∀ {p′ μ} → _} lr₁ lr₂
               ×
             _≡_ {A = ∀ {q′ μ} → _} rl₁ rl₂) →
   ∀ {p′q′} →
   ((pos : ∃ λ μ → ∃ λ (p⟶p′ : p [ μ ]⟶ proj₁ p′q′) →
           proj₁ (lr₁ p⟶p′) ≡ proj₂ p′q′) →
    [ i ] f₁ (inj₁ pos) ≡′
          f₂ (inj₁ (subst (λ lr →
                             ∃ λ μ → ∃ λ (p⟶p′ : p [ μ ]⟶ proj₁ p′q′) →
                             proj₁ (lr p⟶p′) ≡ proj₂ p′q′)
                          (proj₁ eq)
                          pos)))
     ×
   ((pos : ∃ λ μ → ∃ λ (q⟶q′ : q [ μ ]⟶ proj₂ p′q′) →
           proj₁ (rl₁ q⟶q′) ≡ proj₁ p′q′) →
    [ i ] f₁ (inj₂ pos) ≡′
          f₂ (inj₂ (subst (λ rl →
                             ∃ λ μ → ∃ λ (q⟶q′ : q [ μ ]⟶ proj₂ p′q′) →
                             proj₁ (rl q⟶q′) ≡ proj₁ p′q′)
                          (proj₂ eq)
                          pos))))                                         ↝⟨ (∃-cong λ _ → implicit-ΠΣ-comm) ⟩

  (∃ λ (eq : _≡_ {A = ∀ {p′ μ} → _} lr₁ lr₂
               ×
             _≡_ {A = ∀ {q′ μ} → _} rl₁ rl₂) →
   (∀ {p′q′} →
    (pos : ∃ λ μ → ∃ λ (p⟶p′ : p [ μ ]⟶ proj₁ p′q′) →
           proj₁ (lr₁ p⟶p′) ≡ proj₂ p′q′) →
    [ i ] f₁ (inj₁ pos) ≡′
          f₂ (inj₁ (subst (λ lr →
                             ∃ λ μ → ∃ λ (p⟶p′ : p [ μ ]⟶ proj₁ p′q′) →
                             proj₁ (lr p⟶p′) ≡ proj₂ p′q′)
                          (proj₁ eq)
                          pos)))
     ×
   (∀ {p′q′} →
    (pos : ∃ λ μ → ∃ λ (q⟶q′ : q [ μ ]⟶ proj₂ p′q′) →
           proj₁ (rl₁ q⟶q′) ≡ proj₁ p′q′) →
    [ i ] f₁ (inj₂ pos) ≡′
          f₂ (inj₂ (subst (λ rl →
                             ∃ λ μ → ∃ λ (q⟶q′ : q [ μ ]⟶ proj₂ p′q′) →
                             proj₁ (rl q⟶q′) ≡ proj₁ p′q′)
                          (proj₂ eq)
                          pos))))                                         ↝⟨ inverse Σ-assoc ⟩

  (∃ λ (eq₁ : _≡_ {A = ∀ {p′ μ} → _} lr₁ lr₂) →
   ∃ λ (eq₂ : _≡_ {A = ∀ {q′ μ} → _} rl₁ rl₂) →
   (∀ {p′q′} →
    (pos : ∃ λ μ → ∃ λ (p⟶p′ : p [ μ ]⟶ proj₁ p′q′) →
           proj₁ (lr₁ p⟶p′) ≡ proj₂ p′q′) →
    [ i ] f₁ (inj₁ pos) ≡′
          f₂ (inj₁ (subst (λ lr →
                             ∃ λ μ → ∃ λ (p⟶p′ : p [ μ ]⟶ proj₁ p′q′) →
                             proj₁ (lr p⟶p′) ≡ proj₂ p′q′)
                          eq₁ pos)))
     ×
   (∀ {p′q′} →
    (pos : ∃ λ μ → ∃ λ (q⟶q′ : q [ μ ]⟶ proj₂ p′q′) →
           proj₁ (rl₁ q⟶q′) ≡ proj₁ p′q′) →
    [ i ] f₁ (inj₂ pos) ≡′
          f₂ (inj₂ (subst (λ rl →
                             ∃ λ μ → ∃ λ (q⟶q′ : q [ μ ]⟶ proj₂ p′q′) →
                             proj₁ (rl q⟶q′) ≡ proj₁ p′q′)
                          eq₂ pos))))                                     ↝⟨ (∃-cong λ _ → ∃-comm) ⟩

  (∃ λ (eq : _≡_ {A = ∀ {p′ μ} → _} lr₁ lr₂) →
   (∀ {p′q′} →
    (pos : ∃ λ μ → ∃ λ (p⟶p′ : p [ μ ]⟶ proj₁ p′q′) →
           proj₁ (lr₁ p⟶p′) ≡ proj₂ p′q′) →
    [ i ] f₁ (inj₁ pos) ≡′
          f₂ (inj₁ (subst (λ lr →
                             ∃ λ μ → ∃ λ (p⟶p′ : p [ μ ]⟶ proj₁ p′q′) →
                             proj₁ (lr p⟶p′) ≡ proj₂ p′q′)
                          eq pos)))
     ×
   ∃ λ (eq : _≡_ {A = ∀ {q′ μ} → _} rl₁ rl₂) →
   (∀ {p′q′} →
    (pos : ∃ λ μ → ∃ λ (q⟶q′ : q [ μ ]⟶ proj₂ p′q′) →
           proj₁ (rl₁ q⟶q′) ≡ proj₁ p′q′) →
    [ i ] f₁ (inj₂ pos) ≡′
          f₂ (inj₂ (subst (λ rl →
                             ∃ λ μ → ∃ λ (q⟶q′ : q [ μ ]⟶ proj₂ p′q′) →
                             proj₁ (rl q⟶q′) ≡ proj₁ p′q′)
                          eq pos))))                                      ↝⟨ Σ-assoc ⟩

  (∃ λ (eq : _≡_ {A = ∀ {p′ μ} → _} lr₁ lr₂) →
   ∀ {p′q′} →
   (pos : ∃ λ μ → ∃ λ (p⟶p′ : p [ μ ]⟶ proj₁ p′q′) →
          proj₁ (lr₁ p⟶p′) ≡ proj₂ p′q′) →
   [ i ] f₁ (inj₁ pos) ≡′
         f₂ (inj₁ (subst (λ lr →
                            ∃ λ μ → ∃ λ (p⟶p′ : p [ μ ]⟶ proj₁ p′q′) →
                            proj₁ (lr p⟶p′) ≡ proj₂ p′q′)
                         eq pos)))
    ×
  (∃ λ (eq : _≡_ {A = ∀ {q′ μ} → _} rl₁ rl₂) →
   ∀ {p′q′} →
   (pos : ∃ λ μ → ∃ λ (q⟶q′ : q [ μ ]⟶ proj₂ p′q′) →
          proj₁ (rl₁ q⟶q′) ≡ proj₁ p′q′) →
   [ i ] f₁ (inj₂ pos) ≡′
         f₂ (inj₂ (subst (λ rl →
                            ∃ λ μ → ∃ λ (q⟶q′ : q [ μ ]⟶ proj₂ p′q′) →
                            proj₁ (rl q⟶q′) ≡ proj₁ p′q′)
                         eq pos)))                                        ↝⟨ (∃-cong λ _ → Bijection.implicit-Π↔Π)
                                                                               ×-cong
                                                                             (∃-cong λ _ → Bijection.implicit-Π↔Π) ⟩
  (∃ λ (eq : _≡_ {A = ∀ {p′ μ} → _} lr₁ lr₂) →
   ∀ p′q′ →
   (pos : ∃ λ μ → ∃ λ (p⟶p′ : p [ μ ]⟶ proj₁ p′q′) →
          proj₁ (lr₁ p⟶p′) ≡ proj₂ p′q′) →
   [ i ] f₁ (inj₁ pos) ≡′
         f₂ (inj₁ (subst (λ lr →
                            ∃ λ μ → ∃ λ (p⟶p′ : p [ μ ]⟶ proj₁ p′q′) →
                            proj₁ (lr p⟶p′) ≡ proj₂ p′q′)
                         eq pos)))
    ×
  (∃ λ (eq : _≡_ {A = ∀ {q′ μ} → _} rl₁ rl₂) →
   ∀ p′q′ →
   (pos : ∃ λ μ → ∃ λ (q⟶q′ : q [ μ ]⟶ proj₂ p′q′) →
          proj₁ (rl₁ q⟶q′) ≡ proj₁ p′q′) →
   [ i ] f₁ (inj₂ pos) ≡′
         f₂ (inj₂ (subst (λ rl →
                            ∃ λ μ → ∃ λ (q⟶q′ : q [ μ ]⟶ proj₂ p′q′) →
                            proj₁ (rl q⟶q′) ≡ proj₁ p′q′)
                         eq pos)))                                        ↝⟨ (∃-cong λ _ → currying)
                                                                               ×-cong
                                                                             (∃-cong λ _ → currying) ⟩
  (∃ λ (eq : _≡_ {A = ∀ {p′ μ} → _} lr₁ lr₂) →
   ∀ p′ q′ →
   (pos : ∃ λ μ → ∃ λ (p⟶p′ : p [ μ ]⟶ p′) →
          proj₁ (lr₁ p⟶p′) ≡ q′) →
   [ i ] f₁ (inj₁ pos) ≡′
         f₂ (inj₁ (subst (λ lr →
                            ∃ λ μ → ∃ λ (p⟶p′ : p [ μ ]⟶ p′) →
                            proj₁ (lr p⟶p′) ≡ q′)
                         eq pos)))
    ×
  (∃ λ (eq : _≡_ {A = ∀ {q′ μ} → _} rl₁ rl₂) →
   ∀ p′ q′ →
   (pos : ∃ λ μ → ∃ λ (q⟶q′ : q [ μ ]⟶ q′) →
          proj₁ (rl₁ q⟶q′) ≡ p′) →
   [ i ] f₁ (inj₂ pos) ≡′
         f₂ (inj₂ (subst (λ rl →
                            ∃ λ μ → ∃ λ (q⟶q′ : q [ μ ]⟶ q′) →
                            proj₁ (rl q⟶q′) ≡ p′)
                         eq pos)))                                        ↝⟨ (∃-cong λ _ → ∀-cong ext λ _ → ∀-cong ext λ _ → currying)
                                                                               ×-cong
                                                                             (∃-cong λ _ → ∀-cong ext λ _ → ∀-cong ext λ _ → currying) ⟩
  (∃ λ (eq : _≡_ {A = ∀ {p′ μ} → _} lr₁ lr₂) →
   ∀ p′ q′ μ →
   (pos : ∃ λ (p⟶p′ : p [ μ ]⟶ p′) → proj₁ (lr₁ p⟶p′) ≡ q′) →
   [ i ] f₁ (inj₁ (μ , pos)) ≡′
         f₂ (inj₁ (subst (λ lr →
                            ∃ λ μ → ∃ λ (p⟶p′ : p [ μ ]⟶ p′) →
                            proj₁ (lr p⟶p′) ≡ q′)
                         eq (μ , pos))))
    ×
  (∃ λ (eq : _≡_ {A = ∀ {q′ μ} → _} rl₁ rl₂) →
   ∀ p′ q′ μ →
   (pos : ∃ λ (q⟶q′ : q [ μ ]⟶ q′) → proj₁ (rl₁ q⟶q′) ≡ p′) →
   [ i ] f₁ (inj₂ (μ , pos)) ≡′
         f₂ (inj₂ (subst (λ rl →
                            ∃ λ μ → ∃ λ (q⟶q′ : q [ μ ]⟶ q′) →
                            proj₁ (rl q⟶q′) ≡ p′)
                         eq (μ , pos))))                                  ↝⟨ (∃-cong λ _ → ∀-cong ext λ _ → ∀-cong ext λ _ → ∀-cong ext λ _ →
                                                                              currying)
                                                                               ×-cong
                                                                             (∃-cong λ _ → ∀-cong ext λ _ → ∀-cong ext λ _ → ∀-cong ext λ _ →
                                                                              currying) ⟩
  (∃ λ (eq : _≡_ {A = ∀ {p′ μ} → _} lr₁ lr₂) →
   ∀ p′ q′ μ (p⟶p′ : p [ μ ]⟶ p′) (≡q′ : proj₁ (lr₁ p⟶p′) ≡ q′) →
   [ i ] f₁ (inj₁ (μ , p⟶p′ , ≡q′)) ≡′
         f₂ (inj₁ (subst (λ lr →
                            ∃ λ μ → ∃ λ (p⟶p′ : p [ μ ]⟶ p′) →
                            proj₁ (lr p⟶p′) ≡ q′)
                         eq (μ , p⟶p′ , ≡q′))))
    ×
  (∃ λ (eq : _≡_ {A = ∀ {q′ μ} → _} rl₁ rl₂) →
   ∀ p′ q′ μ (q⟶q′ : q [ μ ]⟶ q′) (≡p′ : proj₁ (rl₁ q⟶q′) ≡ p′) →
   [ i ] f₁ (inj₂ (μ , q⟶q′ , ≡p′)) ≡′
         f₂ (inj₂ (subst (λ rl →
                            ∃ λ μ → ∃ λ (q⟶q′ : q [ μ ]⟶ q′) →
                            proj₁ (rl q⟶q′) ≡ p′)
                         eq (μ , q⟶q′ , ≡p′))))                           ↝⟨ (∃-cong λ _ → ∀-cong ext λ _ → Π-comm)
                                                                               ×-cong
                                                                             (∃-cong λ _ → Π-comm) ⟩
  (∃ λ (eq : _≡_ {A = ∀ {p′ μ} → _} lr₁ lr₂) →
   ∀ p′ μ q′ (p⟶p′ : p [ μ ]⟶ p′) (≡q′ : proj₁ (lr₁ p⟶p′) ≡ q′) →
   [ i ] f₁ (inj₁ (μ , p⟶p′ , ≡q′)) ≡′
         f₂ (inj₁ (subst (λ lr →
                            ∃ λ μ → ∃ λ (p⟶p′ : p [ μ ]⟶ p′) →
                            proj₁ (lr p⟶p′) ≡ q′)
                         eq (μ , p⟶p′ , ≡q′))))
    ×
  (∃ λ (eq : _≡_ {A = ∀ {q′ μ} → _} rl₁ rl₂) →
   ∀ q′ p′ μ (q⟶q′ : q [ μ ]⟶ q′) (≡p′ : proj₁ (rl₁ q⟶q′) ≡ p′) →
   [ i ] f₁ (inj₂ (μ , q⟶q′ , ≡p′)) ≡′
         f₂ (inj₂ (subst (λ rl →
                            ∃ λ μ → ∃ λ (q⟶q′ : q [ μ ]⟶ q′) →
                            proj₁ (rl q⟶q′) ≡ p′)
                         eq (μ , q⟶q′ , ≡p′))))                           ↝⟨ (∃-cong λ _ → ∀-cong ext λ _ → ∀-cong ext λ _ → Π-comm)
                                                                               ×-cong
                                                                             (∃-cong λ _ → ∀-cong ext λ _ → Π-comm) ⟩
  (∃ λ (eq : _≡_ {A = ∀ {p′ μ} → _} lr₁ lr₂) →
   ∀ p′ μ (p⟶p′ : p [ μ ]⟶ p′) q′ (≡q′ : proj₁ (lr₁ p⟶p′) ≡ q′) →
   [ i ] f₁ (inj₁ (μ , p⟶p′ , ≡q′)) ≡′
         f₂ (inj₁ (subst (λ lr →
                            ∃ λ μ → ∃ λ (p⟶p′ : p [ μ ]⟶ p′) →
                            proj₁ (lr p⟶p′) ≡ q′)
                         eq (μ , p⟶p′ , ≡q′))))
    ×
  (∃ λ (eq : _≡_ {A = ∀ {q′ μ} → _} rl₁ rl₂) →
   ∀ q′ μ p′ (q⟶q′ : q [ μ ]⟶ q′) (≡p′ : proj₁ (rl₁ q⟶q′) ≡ p′) →
   [ i ] f₁ (inj₂ (μ , q⟶q′ , ≡p′)) ≡′
         f₂ (inj₂ (subst (λ rl →
                            ∃ λ μ → ∃ λ (q⟶q′ : q [ μ ]⟶ q′) →
                            proj₁ (rl q⟶q′) ≡ p′)
                         eq (μ , q⟶q′ , ≡p′))))                           ↝⟨ F.id
                                                                               ×-cong
                                                                             (∃-cong λ _ → ∀-cong ext λ _ → ∀-cong ext λ _ → Π-comm) ⟩
  (∃ λ (eq : _≡_ {A = ∀ {p′ μ} → _} lr₁ lr₂) →
   ∀ p′ μ (p⟶p′ : p [ μ ]⟶ p′) q′ (≡q′ : proj₁ (lr₁ p⟶p′) ≡ q′) →
   [ i ] f₁ (inj₁ (μ , p⟶p′ , ≡q′)) ≡′
         f₂ (inj₁ (subst (λ lr →
                            ∃ λ μ → ∃ λ (p⟶p′ : p [ μ ]⟶ p′) →
                            proj₁ (lr p⟶p′) ≡ q′)
                         eq (μ , p⟶p′ , ≡q′))))
    ×
  (∃ λ (eq : _≡_ {A = ∀ {q′ μ} → _} rl₁ rl₂) →
   ∀ q′ μ (q⟶q′ : q [ μ ]⟶ q′) p′ (≡p′ : proj₁ (rl₁ q⟶q′) ≡ p′) →
   [ i ] f₁ (inj₂ (μ , q⟶q′ , ≡p′)) ≡′
         f₂ (inj₂ (subst (λ rl →
                            ∃ λ μ → ∃ λ (q⟶q′ : q [ μ ]⟶ q′) →
                            proj₁ (rl q⟶q′) ≡ p′)
                         eq (μ , q⟶q′ , ≡p′))))                           ↝⟨ (∃-cong λ _ → ∀-cong ext λ _ → ∀-cong ext λ _ → ∀-cong ext λ _ →
                                                                              inverse $ ∀-intro ext _)
                                                                               ×-cong
                                                                             (∃-cong λ _ → ∀-cong ext λ _ → ∀-cong ext λ _ → ∀-cong ext λ _ →
                                                                              inverse $ ∀-intro ext _) ⟩
  (∃ λ (eq : _≡_ {A = ∀ {p′ μ} → _} lr₁ lr₂) →
   ∀ p′ μ (p⟶p′ : p [ μ ]⟶ p′) →
   [ i ] f₁ (inj₁ (μ , p⟶p′ , refl)) ≡′
         f₂ (inj₁ (subst (λ lr →
                            ∃ λ μ → ∃ λ (p⟶p′′ : p [ μ ]⟶ p′) →
                            proj₁ (lr p⟶p′′) ≡ proj₁ (lr₁ p⟶p′))
                         eq (μ , p⟶p′ , refl))))
    ×
  (∃ λ (eq : _≡_ {A = ∀ {q′ μ} → _} rl₁ rl₂) →
   ∀ q′ μ (q⟶q′ : q [ μ ]⟶ q′) →
   [ i ] f₁ (inj₂ (μ , q⟶q′ , refl)) ≡′
         f₂ (inj₂ (subst (λ rl →
                            ∃ λ μ → ∃ λ (q⟶q′′ : q [ μ ]⟶ q′) →
                            proj₁ (rl q⟶q′′) ≡ proj₁ (rl₁ q⟶q′))
                         eq (μ , q⟶q′ , refl))))                          ↝⟨ (∃-cong λ eq → ∀-cong ext λ _ → ∀-cong ext λ _ → ∀-cong ext λ _ →
                                                                              ≡⇒↝ _ $ cong (([ _ ] f₁ _ ≡′_) ∘ f₂ ∘ inj₁) $ lemma₂ _[_]↝₁_ eq)
                                                                               ×-cong
                                                                             (∃-cong λ eq → ∀-cong ext λ _ → ∀-cong ext λ _ → ∀-cong ext λ _ →
                                                                              ≡⇒↝ _ $ cong (([ _ ] f₁ _ ≡′_) ∘ f₂ ∘ inj₂) $ lemma₂ _[_]↝₂_ eq) ⟩
  (∃ λ (eq : (λ {p′ μ} → lr₁ {p′ = p′} {μ = μ}) ≡ lr₂) →
   ∀ p′ μ (p⟶p′ : p [ μ ]⟶ p′) →
   [ i ] f₁ (inj₁ (μ , p⟶p′ , refl)) ≡′
         f₂ (inj₁ ( μ
                  , p⟶p′
                  , sym (cong (λ lr → proj₁ (lr p⟶p′)) eq)
                  )))
    ×
  (∃ λ (eq : (λ {q′ μ} → rl₁ {q′ = q′} {μ = μ}) ≡ rl₂) →
   ∀ q′ μ (q⟶q′ : q [ μ ]⟶ q′) →
   [ i ] f₁ (inj₂ (μ , q⟶q′ , refl)) ≡′
         f₂ (inj₂ ( μ
                  , q⟶q′
                  , sym (cong (λ rl → proj₁ (rl q⟶q′)) eq)
                  )))                                                     ↝⟨ (∃-cong λ eq → ∀-cong ext λ _ → inverse Bijection.implicit-Π↔Π)
                                                                               ×-cong
                                                                             (∃-cong λ eq → ∀-cong ext λ _ → inverse Bijection.implicit-Π↔Π) ⟩
  (∃ λ (eq : (λ {p′ μ} → lr₁ {p′ = p′} {μ = μ}) ≡ lr₂) →
   ∀ p′ {μ} (p⟶p′ : p [ μ ]⟶ p′) →
   [ i ] f₁ (inj₁ (μ , p⟶p′ , refl)) ≡′
         f₂ (inj₁ ( μ
                  , p⟶p′
                  , sym (cong (λ lr → proj₁ (lr p⟶p′)) eq)
                  )))
    ×
  (∃ λ (eq : (λ {q′ μ} → rl₁ {q′ = q′} {μ = μ}) ≡ rl₂) →
   ∀ q′ {μ} (q⟶q′ : q [ μ ]⟶ q′) →
   [ i ] f₁ (inj₂ (μ , q⟶q′ , refl)) ≡′
         f₂ (inj₂ ( μ
                  , q⟶q′
                  , sym (cong (λ rl → proj₁ (rl q⟶q′)) eq)
                  )))                                                     ↝⟨ (∃-cong λ eq → inverse Bijection.implicit-Π↔Π)
                                                                               ×-cong
                                                                             (∃-cong λ eq → inverse Bijection.implicit-Π↔Π) ⟩
  (∃ λ (eq : (λ {p′ μ} → lr₁ {p′ = p′} {μ = μ}) ≡ lr₂) →
   ∀ {p′ μ} (p⟶p′ : p [ μ ]⟶ p′) →
   [ i ] f₁ (inj₁ (μ , p⟶p′ , refl)) ≡′
         f₂ (inj₁ (μ , p⟶p′ , sym (cong (λ lr → proj₁ (lr p⟶p′)) eq))))
    ×
  (∃ λ (eq : (λ {q′ μ} → rl₁ {q′ = q′} {μ = μ}) ≡ rl₂) →
   ∀ {q′ μ} (q⟶q′ : q [ μ ]⟶ q′) →
   [ i ] f₁ (inj₂ (μ , q⟶q′ , refl)) ≡′
         f₂ (inj₂ (μ , q⟶q′ , sym (cong (λ rl → proj₁ (rl q⟶q′)) eq))))   ↝⟨ (Σ-cong (inverse $ implicit-extensionality-isomorphism
                                                                                                  {k = bijection} ext) λ eq →
                                                                              implicit-∀-cong ext $ implicit-∀-cong ext $ ∀-cong ext λ p⟶p′ →
                                                                              ≡⇒↝ _ $ sym $
                                                                              cong (λ eq → [ _ ] f₁ _ ≡′
                                                                                                 f₂ (inj₁ (_ , p⟶p′ ,
                                                                                                       sym (cong (λ lr → proj₁ (lr p⟶p′)) eq)))) $
                                                                              _↔_.right-inverse-of (implicit-extensionality-isomorphism ext) eq)
                                                                               ×-cong
                                                                             (Σ-cong (inverse $ implicit-extensionality-isomorphism
                                                                                                  {k = bijection} ext) λ eq →
                                                                              implicit-∀-cong ext $ implicit-∀-cong ext $ ∀-cong ext λ q⟶q′ →
                                                                              ≡⇒↝ _ $ sym $
                                                                              cong (λ eq → [ _ ] f₁ _ ≡′
                                                                                                 f₂ (inj₂ (_ , q⟶q′ ,
                                                                                                       sym (cong (λ rl → proj₁ (rl q⟶q′)) eq)))) $
                                                                              _↔_.right-inverse-of (implicit-extensionality-isomorphism ext) eq) ⟩
  (∃ λ (eq : ∀ p′ → (λ {μ} → lr₁ {p′ = p′} {μ = μ}) ≡ lr₂) →
   let eq′ = _↔_.to (implicit-extensionality-isomorphism ext) eq in
   ∀ {p′ μ} (p⟶p′ : p [ μ ]⟶ p′) →
   [ i ] f₁ (inj₁ (μ , p⟶p′ , refl)) ≡′
         f₂ (inj₁ (μ , p⟶p′ , sym (cong (λ lr → proj₁ (lr p⟶p′)) eq′))))
    ×
  (∃ λ (eq : ∀ q′ → (λ {μ} → rl₁ {q′ = q′} {μ = μ}) ≡ rl₂) →
   let eq′ = _↔_.to (implicit-extensionality-isomorphism ext) eq in
   ∀ {q′ μ} (q⟶q′ : q [ μ ]⟶ q′) →
   [ i ] f₁ (inj₂ (μ , q⟶q′ , refl)) ≡′
         f₂ (inj₂ (μ , q⟶q′ , sym (cong (λ rl → proj₁ (rl q⟶q′)) eq′))))  ↝⟨ (∃-cong λ eq →
                                                                              implicit-∀-cong ext $ implicit-∀-cong ext $ ∀-cong ext λ p⟶p′ →
                                                                              ≡⇒↝ _ $ cong (λ eq → [ _ ] f₁ _ ≡′ f₂ (inj₁ (_ , p⟶p′ , sym eq))) $
                                                                              lemma₃ _[_]↝₁_ eq)
                                                                               ×-cong
                                                                             (∃-cong λ eq →
                                                                              implicit-∀-cong ext $ implicit-∀-cong ext $ ∀-cong ext λ q⟶q′ →
                                                                              ≡⇒↝ _ $ cong (λ eq → [ _ ] f₁ _ ≡′ f₂ (inj₂ (_ , q⟶q′ , sym eq))) $
                                                                              lemma₃ _[_]↝₂_ eq) ⟩
  (∃ λ (eq : ∀ p′ → (λ {μ} → lr₁ {p′ = p′} {μ = μ}) ≡ lr₂) →
   ∀ {p′ μ} (p⟶p′ : p [ μ ]⟶ p′) →
   [ i ] f₁ (inj₁ (μ , p⟶p′ , refl)) ≡′
         f₂ (inj₁ (μ , p⟶p′ , sym (cong (λ lr → proj₁ (lr p′ p⟶p′))
                                        (Eq.good-ext ext eq)))))
    ×
  (∃ λ (eq : ∀ q′ → (λ {μ} → rl₁ {q′ = q′} {μ = μ}) ≡ rl₂) →
   ∀ {q′ μ} (q⟶q′ : q [ μ ]⟶ q′) →
   [ i ] f₁ (inj₂ (μ , q⟶q′ , refl)) ≡′
         f₂ (inj₂ (μ , q⟶q′ , sym (cong (λ rl → proj₁ (rl q′ q⟶q′))
                                        (Eq.good-ext ext eq)))))          ↝⟨ (Σ-cong (inverse $ ∀-cong ext λ _ →
                                                                                      implicit-extensionality-isomorphism
                                                                                        {k = bijection} ext) λ eq →
                                                                              implicit-∀-cong ext $ implicit-∀-cong ext $ ∀-cong ext λ p⟶p′ →
                                                                              ≡⇒↝ _ $ sym $
                                                                              cong (λ eq → [ _ ] f₁ _ ≡′
                                                                                                 f₂ (inj₁ (_ , p⟶p′
                                                                                                             , sym (cong (λ lr → proj₁ (lr _ p⟶p′))
                                                                                                                         (Eq.good-ext ext eq))))) $
                                                                              ext (_↔_.right-inverse-of
                                                                                     (implicit-extensionality-isomorphism ext) ∘ eq))
                                                                               ×-cong
                                                                             (Σ-cong (inverse $ ∀-cong ext λ _ →
                                                                                      implicit-extensionality-isomorphism
                                                                                        {k = bijection} ext) λ eq →
                                                                              implicit-∀-cong ext $ implicit-∀-cong ext $ ∀-cong ext λ q⟶q′ →
                                                                              ≡⇒↝ _ $ sym $
                                                                              cong (λ eq → [ _ ] f₁ _ ≡′
                                                                                                 f₂ (inj₂ (_ , q⟶q′
                                                                                                             , sym (cong (λ rl → proj₁ (rl _ q⟶q′))
                                                                                                                         (Eq.good-ext ext eq))))) $
                                                                              ext (_↔_.right-inverse-of
                                                                                     (implicit-extensionality-isomorphism ext) ∘ eq)) ⟩
  (∃ λ (eq : ∀ p′ μ → lr₁ {p′ = p′} {μ = μ} ≡ lr₂) →
   let eq′ = implicit-extensionality (Eq.good-ext ext) ∘ eq in
   ∀ {p′ μ} (p⟶p′ : p [ μ ]⟶ p′) →
   [ i ] f₁ (inj₁ (μ , p⟶p′ , refl)) ≡′
         f₂ (inj₁ (μ , p⟶p′ , sym (cong (λ lr → proj₁ (lr p′ p⟶p′))
                                        (Eq.good-ext ext eq′)))))
    ×
  (∃ λ (eq : ∀ q′ μ → rl₁ {q′ = q′} {μ = μ} ≡ rl₂) →
   let eq′ = implicit-extensionality (Eq.good-ext ext) ∘ eq in
   ∀ {q′ μ} (q⟶q′ : q [ μ ]⟶ q′) →
   [ i ] f₁ (inj₂ (μ , q⟶q′ , refl)) ≡′
         f₂ (inj₂ (μ , q⟶q′ , sym (cong (λ rl → proj₁ (rl q′ q⟶q′))
                                        (Eq.good-ext ext eq′)))))         ↝⟨ (∃-cong λ _ →
                                                                              implicit-∀-cong ext $ implicit-∀-cong ext $ ∀-cong ext λ _ →
                                                                              ≡⇒↝ _ $ cong (λ eq → [ _ ] f₁ _ ≡′ f₂ (inj₁ (_ , _ , sym eq))) $
                                                                              lemma₄ _[_]↝₁_ _)
                                                                               ×-cong
                                                                             (∃-cong λ _ →
                                                                              implicit-∀-cong ext $ implicit-∀-cong ext $ ∀-cong ext λ _ →
                                                                              ≡⇒↝ _ $ cong (λ eq → [ _ ] f₁ _ ≡′ f₂ (inj₂ (_ , _ , sym eq))) $
                                                                              lemma₄ _[_]↝₂_ _) ⟩
  (∃ λ (eq : ∀ p′ μ → lr₁ {p′ = p′} {μ = μ} ≡ lr₂) →
   ∀ {p′ μ} (p⟶p′ : p [ μ ]⟶ p′) →
   [ i ] f₁ (inj₁ (μ , p⟶p′ , refl)) ≡′
         f₂ (inj₁ (μ , p⟶p′
                     , sym (cong (λ lr → proj₁ (lr p⟶p′)) (eq p′ μ)))))
    ×
  (∃ λ (eq : ∀ q′ μ → rl₁ {q′ = q′} {μ = μ} ≡ rl₂) →
   ∀ {q′ μ} (q⟶q′ : q [ μ ]⟶ q′) →
   [ i ] f₁ (inj₂ (μ , q⟶q′ , refl)) ≡′
         f₂ (inj₂ (μ , q⟶q′
                     , sym (cong (λ rl → proj₁ (rl q⟶q′)) (eq q′ μ)))))   ↝⟨ Σ-cong (inverse Bijection.implicit-Π↔Π) (λ _ → F.id)
                                                                               ×-cong
                                                                             Σ-cong (inverse Bijection.implicit-Π↔Π) (λ _ → F.id) ⟩
  (∃ λ (eq : ∀ {p′} μ → lr₁ {p′ = p′} {μ = μ} ≡ lr₂) →
   ∀ {p′ μ} (p⟶p′ : p [ μ ]⟶ p′) →
   [ i ] f₁ (inj₁ (μ , p⟶p′ , refl)) ≡′
         f₂ (inj₁ (μ , p⟶p′
                     , sym (cong (λ lr → proj₁ (lr p⟶p′)) (eq μ)))))
    ×
  (∃ λ (eq : ∀ {q′} μ → rl₁ {q′ = q′} {μ = μ} ≡ rl₂) →
   ∀ {q′ μ} (q⟶q′ : q [ μ ]⟶ q′) →
   [ i ] f₁ (inj₂ (μ , q⟶q′ , refl)) ≡′
         f₂ (inj₂ (μ , q⟶q′
                     , sym (cong (λ rl → proj₁ (rl q⟶q′)) (eq μ)))))      ↝⟨ Σ-cong (implicit-∀-cong ext $ inverse Bijection.implicit-Π↔Π)
                                                                                    (λ _ → F.id)
                                                                               ×-cong
                                                                             Σ-cong (implicit-∀-cong ext $ inverse Bijection.implicit-Π↔Π)
                                                                                    (λ _ → F.id) ⟩
  (∃ λ (eq : ∀ {p′ μ} → lr₁ {p′ = p′} {μ = μ} ≡ lr₂) →
   ∀ {p′ μ} (p⟶p′ : p [ μ ]⟶ p′) →
   [ i ] f₁ (inj₁ (μ , p⟶p′ , refl)) ≡′
         f₂ (inj₁ (μ , p⟶p′
                     , sym (cong (λ lr → proj₁ (lr p⟶p′)) eq))))
    ×
  (∃ λ (eq : ∀ {q′ μ} → rl₁ {q′ = q′} {μ = μ} ≡ rl₂) →
   ∀ {q′ μ} (q⟶q′ : q [ μ ]⟶ q′) →
   [ i ] f₁ (inj₂ (μ , q⟶q′ , refl)) ≡′
         f₂ (inj₂ (μ , q⟶q′
                     , sym (cong (λ rl → proj₁ (rl q⟶q′)) eq))))          ↝⟨ (∃-cong λ eq →
                                                                              implicit-∀-cong ext $ implicit-∀-cong ext $ ∀-cong ext λ p⟶p′ →
                                                                              ≡⇒↝ _ $ cong (λ eq → [ _ ] f₁ _ ≡′ f₂ (inj₁ (_ , _ , sym eq))) $ sym $
                                                                              cong-∘ proj₁ (_$ p⟶p′) (eq {μ = _}))
                                                                               ×-cong
                                                                             (∃-cong λ eq →
                                                                              implicit-∀-cong ext $ implicit-∀-cong ext $ ∀-cong ext λ q⟶q′ →
                                                                              ≡⇒↝ _ $ cong (λ eq → [ _ ] f₁ _ ≡′ f₂ (inj₂ (_ , _ , sym eq))) $ sym $
                                                                              cong-∘ proj₁ (_$ q⟶q′) (eq {μ = _})) ⟩
  (∃ λ (eq : ∀ {p′ μ} → lr₁ {p′ = p′} {μ = μ} ≡ lr₂) →
   ∀ {p′ μ} (p⟶p′ : p [ μ ]⟶ p′) →
   [ i ] f₁ (inj₁ (μ , p⟶p′ , refl)) ≡′
         f₂ (inj₁ (μ , p⟶p′ , sym (cong proj₁ $ cong (_$ p⟶p′) eq))))
    ×
  (∃ λ (eq : ∀ {q′ μ} → rl₁ {q′ = q′} {μ = μ} ≡ rl₂) →
   ∀ {q′ μ} (q⟶q′ : q [ μ ]⟶ q′) →
   [ i ] f₁ (inj₂ (μ , q⟶q′ , refl)) ≡′
         f₂ (inj₂ (μ , q⟶q′ , sym (cong proj₁ $ cong (_$ q⟶q′) eq))))     ↝⟨ Σ-cong (implicit-∀-cong ext $ implicit-∀-cong ext $ inverse $
                                                                                     Eq.extensionality-isomorphism ext)
                                                                                    (λ _ → F.id)
                                                                               ×-cong
                                                                             Σ-cong (implicit-∀-cong ext $ implicit-∀-cong ext $ inverse $
                                                                                     Eq.extensionality-isomorphism ext)
                                                                                    (λ _ → F.id) ⟩
  (∃ λ (eq : ∀ {p′ μ} (p⟶p′ : p [ μ ]⟶ p′) →
             lr₁ p⟶p′ ≡ lr₂ p⟶p′) →
   ∀ {p′ μ} (p⟶p′ : p [ μ ]⟶ p′) →
   [ i ] f₁ (inj₁ (μ , p⟶p′ , refl)) ≡′
         f₂ (inj₁ (μ , p⟶p′ , sym (cong proj₁ (eq p⟶p′)))))
    ×
  (∃ λ (eq : ∀ {q′ μ} (q⟶q′ : q [ μ ]⟶ q′) →
             rl₁ q⟶q′ ≡ rl₂ q⟶q′) →
   ∀ {q′ μ} (q⟶q′ : q [ μ ]⟶ q′) →
   [ i ] f₁ (inj₂ (μ , q⟶q′ , refl)) ≡′
         f₂ (inj₂ (μ , q⟶q′ , sym (cong proj₁ (eq q⟶q′)))))               ↝⟨ inverse implicit-ΠΣ-comm
                                                                               ×-cong
                                                                             inverse implicit-ΠΣ-comm ⟩
  (∀ {p′} →
   ∃ λ (eq : ∀ {μ} (p⟶p′ : p [ μ ]⟶ p′) →
             lr₁ p⟶p′ ≡ lr₂ p⟶p′) →
   ∀ {μ} (p⟶p′ : p [ μ ]⟶ p′) →
   [ i ] f₁ (inj₁ (μ , p⟶p′ , refl)) ≡′
         f₂ (inj₁ (μ , p⟶p′ , sym (cong proj₁ (eq p⟶p′)))))
    ×
  (∀ {q′} →
   ∃ λ (eq : ∀ {μ} (q⟶q′ : q [ μ ]⟶ q′) →
             rl₁ q⟶q′ ≡ rl₂ q⟶q′) →
   ∀ {μ} (q⟶q′ : q [ μ ]⟶ q′) →
   [ i ] f₁ (inj₂ (μ , q⟶q′ , refl)) ≡′
         f₂ (inj₂ (μ , q⟶q′ , sym (cong proj₁ (eq q⟶q′)))))               ↝⟨ (implicit-∀-cong ext $ inverse implicit-ΠΣ-comm)
                                                                               ×-cong
                                                                             (implicit-∀-cong ext $ inverse implicit-ΠΣ-comm) ⟩
  (∀ {p′ μ} →
   ∃ λ (eq : (p⟶p′ : p [ μ ]⟶ p′) → lr₁ p⟶p′ ≡ lr₂ p⟶p′) →
   ∀ p⟶p′ → [ i ] f₁ (inj₁ (μ , p⟶p′ , refl)) ≡′
                  f₂ (inj₁ (μ , p⟶p′ , sym (cong proj₁ (eq p⟶p′)))))
    ×
  (∀ {q′ μ} →
   ∃ λ (eq : (q⟶q′ : q [ μ ]⟶ q′) → rl₁ q⟶q′ ≡ rl₂ q⟶q′) →
   ∀ q⟶q′ → [ i ] f₁ (inj₂ (μ , q⟶q′ , refl)) ≡′
                  f₂ (inj₂ (μ , q⟶q′ , sym (cong proj₁ (eq q⟶q′)))))      ↝⟨ (implicit-∀-cong ext $ implicit-∀-cong ext $ inverse ΠΣ-comm)
                                                                               ×-cong
                                                                             (implicit-∀-cong ext $ implicit-∀-cong ext $ inverse ΠΣ-comm) ⟩
  (∀ {p′ μ} (p⟶p′ : p [ μ ]⟶ p′) →
   ∃ λ (eq : lr₁ p⟶p′ ≡ lr₂ p⟶p′) →
   [ i ] f₁ (inj₁ (μ , p⟶p′ , refl)) ≡′
         f₂ (inj₁ (μ , p⟶p′ , sym (cong proj₁ eq))))
    ×
  (∀ {q′ μ} (q⟶q′ : q [ μ ]⟶ q′) →
   ∃ λ (eq : rl₁ q⟶q′ ≡ rl₂ q⟶q′) →
   [ i ] f₁ (inj₂ (μ , q⟶q′ , refl)) ≡′
         f₂ (inj₂ (μ , q⟶q′ , sym (cong proj₁ eq))))                      ↝⟨ inverse $
                                                                             (implicit-∀-cong ext $ implicit-∀-cong ext $ ∀-cong ext λ _ →
                                                                              Σ-cong Bijection.Σ-≡,≡↔≡ λ _ → F.id)
                                                                               ×-cong
                                                                             (implicit-∀-cong ext $ implicit-∀-cong ext $ ∀-cong ext λ _ →
                                                                              Σ-cong Bijection.Σ-≡,≡↔≡ λ _ → F.id) ⟩
  (∀ {p′ μ} (p⟶p′ : p [ μ ]⟶ p′) →
   let q′₁ , q⟶q′₁ = lr₁ p⟶p′
       q′₂ , q⟶q′₂ = lr₂ p⟶p′
   in ∃ λ (eq : ∃ λ (q′₁≡q′₂ : q′₁ ≡ q′₂) →
                  subst (q [ μ ]↝₁_) q′₁≡q′₂ q⟶q′₁ ≡ q⟶q′₂) →
      [ i ] f₁ (inj₁ (μ , p⟶p′ , refl)) ≡′
            f₂ (inj₁ (μ , p⟶p′
                        , sym (cong proj₁ (uncurry Σ-≡,≡→≡ eq)))))
    ×
  (∀ {q′ μ} (q⟶q′ : q [ μ ]⟶ q′) →
   let p′₁ , p⟶p′₁ = rl₁ q⟶q′
       p′₂ , p⟶p′₂ = rl₂ q⟶q′
   in ∃ λ (eq : ∃ λ (p′₁≡p′₂ : p′₁ ≡ p′₂) →
                  subst (p [ μ ]↝₂_) p′₁≡p′₂ p⟶p′₁ ≡ p⟶p′₂) →
      [ i ] f₁ (inj₂ (μ , q⟶q′ , refl)) ≡′
            f₂ (inj₂ (μ , q⟶q′
                        , sym (cong proj₁ (uncurry Σ-≡,≡→≡ eq)))))        ↝⟨ (implicit-∀-cong ext $ implicit-∀-cong ext $ ∀-cong ext λ _ →
                                                                              ∃-cong λ eq →
                                                                              ≡⇒↝ _ $ cong (λ eq → [ _ ] f₁ _ ≡′ f₂ (inj₁ (_ , _ , sym eq))) $
                                                                              proj₁-Σ-≡,≡→≡ (proj₁ eq) (proj₂ eq))
                                                                               ×-cong
                                                                             (implicit-∀-cong ext $ implicit-∀-cong ext $ ∀-cong ext λ _ →
                                                                              ∃-cong λ eq →
                                                                              ≡⇒↝ _ $ cong (λ eq → [ _ ] f₁ _ ≡′ f₂ (inj₂ (_ , _ , sym eq))) $
                                                                              proj₁-Σ-≡,≡→≡ (proj₁ eq) (proj₂ eq)) ⟩
  (∀ {p′ μ} (p⟶p′ : p [ μ ]⟶ p′) →
   let q′₁ , q⟶q′₁ = lr₁ p⟶p′
       q′₂ , q⟶q′₂ = lr₂ p⟶p′
   in ∃ λ (eq : ∃ λ (q′₁≡q′₂ : q′₁ ≡ q′₂) →
                  subst (q [ μ ]↝₁_) q′₁≡q′₂ q⟶q′₁ ≡ q⟶q′₂) →
      [ i ] f₁ (inj₁ (μ , p⟶p′ , refl)) ≡′
            f₂ (inj₁ (μ , p⟶p′ , sym (proj₁ eq))))
    ×
  (∀ {q′ μ} (q⟶q′ : q [ μ ]⟶ q′) →
   let p′₁ , p⟶p′₁ = rl₁ q⟶q′
       p′₂ , p⟶p′₂ = rl₂ q⟶q′
   in ∃ λ (eq : ∃ λ (p′₁≡p′₂ : p′₁ ≡ p′₂) →
                  subst (p [ μ ]↝₂_) p′₁≡p′₂ p⟶p′₁ ≡ p⟶p′₂) →
      [ i ] f₁ (inj₂ (μ , q⟶q′ , refl)) ≡′
            f₂ (inj₂ (μ , q⟶q′ , sym (proj₁ eq))))                        ↝⟨ (implicit-∀-cong ext $ implicit-∀-cong ext $ ∀-cong ext λ _ →
                                                                              inverse Σ-assoc)
                                                                               ×-cong
                                                                             (implicit-∀-cong ext $ implicit-∀-cong ext $ ∀-cong ext λ _ →
                                                                              inverse Σ-assoc) ⟩
  (∀ {p′ μ} (p⟶p′ : p [ μ ]⟶ p′) →
   let q′₁ , q⟶q′₁ = lr₁ p⟶p′
       q′₂ , q⟶q′₂ = lr₂ p⟶p′
   in ∃ λ (q′₁≡q′₂ : q′₁ ≡ q′₂) →
        subst (q [ μ ]↝₁_) q′₁≡q′₂ q⟶q′₁ ≡ q⟶q′₂
          ×
        [ i ] f₁ (inj₁ (μ , p⟶p′ , refl)) ≡′
              f₂ (inj₁ (μ , p⟶p′ , sym q′₁≡q′₂)))
    ×
  (∀ {q′ μ} (q⟶q′ : q [ μ ]⟶ q′) →
   let p′₁ , p⟶p′₁ = rl₁ q⟶q′
       p′₂ , p⟶p′₂ = rl₂ q⟶q′
   in ∃ λ (p′₁≡p′₂ : p′₁ ≡ p′₂) →
        subst (p [ μ ]↝₂_) p′₁≡p′₂ p⟶p′₁ ≡ p⟶p′₂
          ×
        [ i ] f₁ (inj₂ (μ , q⟶q′ , refl)) ≡′
              f₂ (inj₂ (μ , q⟶q′ , sym p′₁≡p′₂)))                         ↝⟨ (implicit-∀-cong ext $ implicit-∀-cong ext $ ∀-cong ext λ p⟶p′ →
                                                                              ∃-cong λ q′₁≡q′₂ → ∃-cong λ _ → ≡⇒↝ _ $
                                                                              lemma₅₁ q′₁≡q′₂)
                                                                               ×-cong
                                                                             (implicit-∀-cong ext $ implicit-∀-cong ext $ ∀-cong ext λ q⟶q′ →
                                                                              ∃-cong λ p′₁≡p′₂ → ∃-cong λ _ → ≡⇒↝ _ $
                                                                              lemma₅₂ p′₁≡p′₂) ⟩
  (∀ {p′ μ} (p⟶p′ : p [ μ ]⟶ p′) →
   let q′₁ , q⟶q′₁ = lr₁ p⟶p′
       q′₂ , q⟶q′₂ = lr₂ p⟶p′
   in ∃ λ (q′₁≡q′₂ : q′₁ ≡ q′₂) →
        subst (q [ μ ]↝₁_) q′₁≡q′₂ q⟶q′₁ ≡ q⟶q′₂
          ×
        [ i ] subst (ν′ S̲t̲e̲p̲ ∞ ∘ (p′ ,_)) q′₁≡q′₂
                    (f₁ (inj₁ (_ , p⟶p′ , refl))) ≡′
              f₂ (inj₁ (_ , p⟶p′ , refl)))
    ×
  (∀ {q′ μ} (q⟶q′ : q [ μ ]⟶ q′) →
   let p′₁ , p⟶p′₁ = rl₁ q⟶q′
       p′₂ , p⟶p′₂ = rl₂ q⟶q′
   in ∃ λ (p′₁≡p′₂ : p′₁ ≡ p′₂) →
        subst (p [ μ ]↝₂_) p′₁≡p′₂ p⟶p′₁ ≡ p⟶p′₂
          ×
        [ i ] subst (ν′ S̲t̲e̲p̲ ∞ ∘ (_, q′)) p′₁≡p′₂
                    (f₁ (inj₂ (_ , q⟶q′ , refl))) ≡′
              f₂ (inj₂ (_ , q⟶q′ , refl)))                                ↔⟨⟩

  (∀ {p′ μ} (p⟶p′ : p [ μ ]⟶ p′) →
   let q′₁ , q⟶q′₁ , p′∼q′₁ = S̲t̲e̲p̲.left-to-right (s₁ , f₁) p⟶p′
       q′₂ , q⟶q′₂ , p′∼q′₂ = S̲t̲e̲p̲.left-to-right (s₂ , f₂) p⟶p′
   in ∃ λ (q′₁≡q′₂ : q′₁ ≡ q′₂) →
        subst (q [ μ ]↝₁_) q′₁≡q′₂ q⟶q′₁ ≡ q⟶q′₂
          ×
        [ i ] subst (ν′ S̲t̲e̲p̲ ∞ ∘ (p′ ,_)) q′₁≡q′₂ p′∼q′₁ ≡′ p′∼q′₂)
    ×
  (∀ {q′ μ} (q⟶q′ : q [ μ ]⟶ q′) →
   let p′₁ , p⟶p′₁ , p′∼q′₁ = S̲t̲e̲p̲.right-to-left (s₁ , f₁) q⟶q′
       p′₂ , p⟶p′₂ , p′∼q′₂ = S̲t̲e̲p̲.right-to-left (s₂ , f₂) q⟶q′
   in ∃ λ (p′₁≡p′₂ : p′₁ ≡ p′₂) →
        subst (p [ μ ]↝₂_) p′₁≡p′₂ p⟶p′₁ ≡ p⟶p′₂
          ×
        [ i ] subst (ν′ S̲t̲e̲p̲ ∞ ∘ (_, q′)) p′₁≡p′₂ p′∼q′₁ ≡′ p′∼q′₂)       □

  where

  lemma₁₁ = λ (eq : _≡_ {A = ∀ {p′ μ} → _} lr₁ lr₂
                      ×
                    _≡_ {A = ∀ {q′ μ} → _} rl₁ rl₂)
              {p′q′} {pos : ∃ λ μ → ∃ λ (p⟶p′ : p [ μ ]⟶ proj₁ p′q′) →
                            proj₁ (lr₁ p⟶p′) ≡ proj₂ p′q′} →

    [ i ] f₁ (inj₁ pos) ≡′
          f₂ (subst (λ s → Container.Position S̲t̲e̲p̲ (_ , s) p′q′)
                    (cong₂ _,_ (proj₁ eq) (proj₂ eq)) (inj₁ pos))         ≡⟨ cong (([ _ ] f₁ _ ≡′_) ∘ f₂) $
                                                                             push-subst-inj₁ {y≡z = cong₂ _,_ (proj₁ eq) (proj₂ eq)} _ _ ⟩
    [ i ] f₁ (inj₁ pos) ≡′
          f₂ (inj₁ (subst (λ s →
                             ∃ λ μ → ∃ λ (p⟶p′ : p [ μ ]⟶ proj₁ p′q′) →
                             proj₁ (proj₁ s p⟶p′) ≡ proj₂ p′q′)
                          (cong₂ _,_ (proj₁ eq) (proj₂ eq)) pos))         ≡⟨ cong (([ _ ] f₁ _ ≡′_) ∘ f₂ ∘ inj₁) $
                                                                             subst-∘ _ _ (cong₂ _,_ (proj₁ eq) (proj₂ eq)) ⟩
    [ i ] f₁ (inj₁ pos) ≡′
          f₂ (inj₁ (subst (λ lr →
                             ∃ λ μ → ∃ λ (p⟶p′ : p [ μ ]⟶ proj₁ p′q′) →
                             proj₁ (lr p⟶p′) ≡ proj₂ p′q′)
                          (cong proj₁ (cong₂ _,_ (proj₁ eq) (proj₂ eq)))
                          pos))                                           ≡⟨ cong (([ _ ] f₁ _ ≡′_) ∘ f₂ ∘ inj₁) $ cong (flip (subst _) _) $
                                                                             cong-proj₁-cong₂-, (proj₁ eq) (proj₂ eq) ⟩∎
    [ i ] f₁ (inj₁ pos) ≡′
          f₂ (inj₁ (subst (λ lr →
                             ∃ λ μ → ∃ λ (p⟶p′ : p [ μ ]⟶ proj₁ p′q′) →
                             proj₁ (lr p⟶p′) ≡ proj₂ p′q′)
                          (proj₁ eq)
                          pos))                                           ∎

  lemma₁₂ = λ (eq : _≡_ {A = ∀ {p′ μ} → _} lr₁ lr₂
                      ×
                    _≡_ {A = ∀ {q′ μ} → _} rl₁ rl₂)
              {p′q′} {pos : ∃ λ μ → ∃ λ (q⟶q′ : q [ μ ]⟶ proj₂ p′q′) →
                            proj₁ (rl₁ q⟶q′) ≡ proj₁ p′q′} →

    [ i ] f₁ (inj₂ pos) ≡′
          f₂ (subst (λ s → Container.Position S̲t̲e̲p̲ (_ , s) p′q′)
                    (cong₂ _,_ (proj₁ eq) (proj₂ eq)) (inj₂ pos))         ≡⟨ cong (([ _ ] f₁ _ ≡′_) ∘ f₂) $
                                                                             push-subst-inj₂ {y≡z = cong₂ _,_ (proj₁ eq) (proj₂ eq)} _ _ ⟩
    [ i ] f₁ (inj₂ pos) ≡′
          f₂ (inj₂ (subst (λ s →
                             ∃ λ μ → ∃ λ (q⟶q′ : q [ μ ]⟶ proj₂ p′q′) →
                             proj₁ (proj₂ s q⟶q′) ≡ proj₁ p′q′)
                          (cong₂ _,_ (proj₁ eq) (proj₂ eq)) pos))         ≡⟨ cong (([ _ ] f₁ _ ≡′_) ∘ f₂ ∘ inj₂) $
                                                                             subst-∘ _ _ (cong₂ _,_ (proj₁ eq) (proj₂ eq)) ⟩
    [ i ] f₁ (inj₂ pos) ≡′
          f₂ (inj₂ (subst (λ rl →
                             ∃ λ μ → ∃ λ (q⟶q′ : q [ μ ]⟶ proj₂ p′q′) →
                             proj₁ (rl q⟶q′) ≡ proj₁ p′q′)
                          (cong proj₂ (cong₂ _,_ (proj₁ eq) (proj₂ eq)))
                          pos))                                           ≡⟨ cong (([ _ ] f₁ _ ≡′_) ∘ f₂ ∘ inj₂) $ cong (flip (subst _) _) $
                                                                             cong-proj₂-cong₂-, (proj₁ eq) (proj₂ eq) ⟩∎
    [ i ] f₁ (inj₂ pos) ≡′
          f₂ (inj₂ (subst (λ rl →
                             ∃ λ μ → ∃ λ (q⟶q′ : q [ μ ]⟶ proj₂ p′q′) →
                             proj₁ (rl q⟶q′) ≡ proj₁ p′q′)
                          (proj₂ eq)
                          pos))                                           ∎

  lemma₂ = λ (_[_]↝_ : Proc → Label → Proc → Set)
             {p q} {f g : ∀ {p′ μ} → p [ μ ]⟶ p′ → ∃ (q [ μ ]↝_)}
             (eq : (λ {p′ μ} → f {p′ = p′} {μ = μ}) ≡ g)
             {p′ μ} {p⟶p′ : p [ μ ]⟶ p′} →

    subst (λ lr →
             ∃ λ μ → ∃ λ (p⟶p′′ : p [ μ ]⟶ p′) →
             proj₁ (lr p⟶p′′) ≡ proj₁ (f p⟶p′))
          eq (μ , p⟶p′ , refl)                          ≡⟨ push-subst-pair′ {y≡z = eq} _ _ _ ⟩

    ( μ
    , subst₂ (λ { (lr , μ) →
                  ∃ λ (p⟶p′′ : p [ μ ]⟶ p′) →
                  proj₁ (lr p⟶p′′) ≡ proj₁ (f p⟶p′) })
             eq (subst-const eq) (p⟶p′ , refl)
    )                                                   ≡⟨ cong (μ ,_) $
                                                           cong (λ eq → subst (λ { (lr , μ) →
                                                                                   ∃ λ (p⟶p′′ : p [ μ ]⟶ p′) →
                                                                                   proj₁ (lr p⟶p′′) ≡ proj₁ (f p⟶p′) })
                                                                              eq (p⟶p′ , refl)) $
                                                           Σ-≡,≡→≡-subst-const eq refl ⟩
    ( μ
    , subst (λ { (lr , μ) →
                 ∃ λ (p⟶p′′ : p [ μ ]⟶ p′) →
                 proj₁ (lr p⟶p′′) ≡ proj₁ (f p⟶p′) })
            (cong₂ _,_ eq refl) (p⟶p′ , refl)
    )                                                   ≡⟨⟩

    ( μ
    , subst (λ { (lr , μ) →
                 ∃ λ (p⟶p′′ : p [ μ ]⟶ p′) →
                 proj₁ (lr p⟶p′′) ≡ proj₁ (f p⟶p′) })
            (cong (_, _) eq) (p⟶p′ , refl)
    )                                                   ≡⟨ cong (μ ,_) $ sym $
                                                           subst-∘ _ _ eq ⟩
    ( μ
    , subst (λ lr →
               ∃ λ (p⟶p′′ : p [ μ ]⟶ p′) →
               proj₁ (lr p⟶p′′) ≡ proj₁ (f p⟶p′))
            eq (p⟶p′ , refl)
    )                                                   ≡⟨ cong (μ ,_) $
                                                           push-subst-pair′ {y≡z = eq} _ _ _ ⟩
    ( μ
    , p⟶p′
    , subst₂ (λ { (lr , p⟶p′′) →
                  proj₁ (lr p⟶p′′) ≡ proj₁ (f p⟶p′) })
             eq (subst-const eq) refl
    )                                                   ≡⟨ cong (λ eq → (_ , p⟶p′ , subst (λ { (lr , p⟶p′′) → proj₁ (lr p⟶p′′) ≡ proj₁ (f p⟶p′) })
                                                                                          eq refl)) $
                                                           Σ-≡,≡→≡-subst-const eq refl ⟩
    ( μ
    , p⟶p′
    , subst (λ { (lr , p⟶p′′) →
                 proj₁ (lr p⟶p′′) ≡ proj₁ (f p⟶p′) })
            (cong (_, _) eq) refl
    )                                                   ≡⟨ cong (λ eq → (_ , p⟶p′ , eq)) $ sym $
                                                           subst-∘ _ _ eq ⟩
    ( μ
    , p⟶p′
    , subst (λ lr → proj₁ (lr p⟶p′) ≡ proj₁ (f p⟶p′))
            eq refl
    )                                                   ≡⟨ cong (λ eq → (_ , p⟶p′ , eq)) $
                                                           subst-∘ _ _ eq ⟩
    ( μ
    , p⟶p′
    , subst (_≡ proj₁ (f p⟶p′))
            (cong (λ lr → proj₁ (lr p⟶p′)) eq) refl
    )                                                   ≡⟨ cong (λ eq → (_ , p⟶p′ , subst (_≡ _) eq refl)) $
                                                           sym $ sym-sym (cong (λ lr → proj₁ (lr p⟶p′)) eq) ⟩
    ( μ
    , p⟶p′
    , subst (_≡ proj₁ (f p⟶p′))
            (sym $ sym $
               cong (λ lr → proj₁ (lr p⟶p′)) eq)
            refl
    )                                                   ≡⟨ cong (λ eq → (_ , p⟶p′ , eq)) $
                                                           subst-trans (sym $ cong (λ lr → proj₁ (lr p⟶p′)) eq) ⟩∎
    ( μ
    , p⟶p′
    , sym (cong (λ lr → proj₁ (lr p⟶p′)) eq)
    )                                                   ∎

  lemma₃ = λ (_[_]↝_ : Proc → Label → Proc → Set)
             {p q} {f g : ∀ {p′ μ} → p [ μ ]⟶ p′ → ∃ (q [ μ ]↝_)}
             (eq : ∀ p′ → (λ {μ} → f {p′ = p′} {μ = μ}) ≡ g)
             {p′ μ} {p⟶p′ : p [ μ ]⟶ p′} →

    cong (λ lr → proj₁ (lr p⟶p′))
         (_↔_.to (implicit-extensionality-isomorphism ext) eq)  ≡⟨⟩

    cong (λ lr → proj₁ (lr p⟶p′))
         (implicit-extensionality (Eq.good-ext ext) eq)         ≡⟨ cong-∘ _ _ (Eq.good-ext ext eq) ⟩∎

    cong (λ lr → proj₁ (lr p′ p⟶p′)) (Eq.good-ext ext eq)       ∎

  lemma₄ = λ (_[_]↝_ : Proc → Label → Proc → Set)
             {p q} {f g : ∀ {p′ μ} → p [ μ ]⟶ p′ → ∃ (q [ μ ]↝_)}
             (eq : ∀ p′ μ → f {p′ = p′} {μ = μ} ≡ g)
             {p′ μ p⟶p′} →

    cong (λ (lr : ∀ _ {μ} → _) → proj₁ (lr p′ {μ = μ} p⟶p′))
         (Eq.good-ext ext
            (implicit-extensionality (Eq.good-ext ext) ∘ eq))     ≡⟨⟩

    cong (λ lr → proj₁ (lr p′ p⟶p′))
         (Eq.good-ext ext
            (cong (λ f {x} → f x) ∘ (Eq.good-ext ext ∘ eq)))      ≡⟨ cong (cong (λ lr → proj₁ (lr p′ p⟶p′))) $ sym $
                                                                     Eq.cong-post-∘-good-ext {h = λ f {x} → f x} ext ext (Eq.good-ext ext ∘ eq) ⟩
    cong (λ lr → proj₁ (lr p′ p⟶p′))
         (cong (λ f x {y} → f x y)
               (Eq.good-ext ext (Eq.good-ext ext ∘ eq)))          ≡⟨ cong-∘ _ _ (Eq.good-ext ext (Eq.good-ext ext ∘ eq)) ⟩

    cong (λ lr → proj₁ (lr p′ μ p⟶p′))
         (Eq.good-ext ext (Eq.good-ext ext ∘ eq))                 ≡⟨ sym $ cong-∘ _ _ (Eq.good-ext ext (Eq.good-ext ext ∘ eq)) ⟩

    cong (λ lr → proj₁ (lr μ p⟶p′))
         (cong (_$ p′) (Eq.good-ext ext (Eq.good-ext ext ∘ eq)))  ≡⟨ cong (cong (λ lr → proj₁ (lr μ p⟶p′))) $ Eq.cong-good-ext ext _ ⟩

    cong (λ lr → proj₁ (lr μ p⟶p′)) (Eq.good-ext ext (eq p′))     ≡⟨ sym $ cong-∘ _ _ (Eq.good-ext ext (eq p′)) ⟩

    cong (λ lr → proj₁ (lr p⟶p′))
         (cong (_$ μ) (Eq.good-ext ext (eq p′)))                  ≡⟨ cong (cong (λ lr → proj₁ (lr p⟶p′))) $ Eq.cong-good-ext ext _ ⟩∎

    cong (λ lr → proj₁ (lr p⟶p′)) (eq p′ μ)                       ∎

  lemma₅₁ :
    ∀ {p′ μ} {p⟶p′ : p [ μ ]⟶ p′}
    (q′₁≡q′₂ : proj₁ (lr₁ p⟶p′) ≡ proj₁ (lr₂ p⟶p′)) →
    ([ i ] f₁ (inj₁ (μ , p⟶p′ , refl)) ≡′
           f₂ (inj₁ (μ , p⟶p′ , sym q′₁≡q′₂)))
      ≡
    ([ i ] subst (ν′ S̲t̲e̲p̲ ∞ ∘ (p′ ,_)) q′₁≡q′₂
                 (f₁ (inj₁ (_ , p⟶p′ , refl))) ≡′
           f₂ (inj₁ (_ , p⟶p′ , refl)))
  lemma₅₁ {p′} {μ} {p⟶p′} q′₁≡q′₂ =
    ([ i ] f₁ (inj₁ (μ , p⟶p′ , refl)) ≡′
           f₂ (inj₁ (μ , p⟶p′ , sym q′₁≡q′₂)))        ≡⟨ cong ([ _ ] f₁ _ ≡′_) $ lemma′ q′₁≡q′₂ ⟩

    ([ i ] f₁ (inj₁ (μ , p⟶p′ , refl)) ≡′
           subst (ν′ S̲t̲e̲p̲ ∞ ∘ (p′ ,_)) (sym q′₁≡q′₂)
                 (f₂ (inj₁ (_ , p⟶p′ , refl))))       ≡⟨ lemma″ q′₁≡q′₂ ⟩∎

    ([ i ] subst (ν′ S̲t̲e̲p̲ ∞ ∘ (p′ ,_)) q′₁≡q′₂
                 (f₁ (inj₁ (_ , p⟶p′ , refl))) ≡′
           f₂ (inj₁ (_ , p⟶p′ , refl)))               ∎
    where
    lemma′ :
      ∀ {q′₁} (q′₁≡q′₂ : q′₁ ≡ proj₁ (lr₂ p⟶p′)) →
      f₂ (inj₁ (μ , p⟶p′ , sym q′₁≡q′₂))
        ≡
      subst (ν′ S̲t̲e̲p̲ ∞ ∘ (p′ ,_)) (sym q′₁≡q′₂)
            (f₂ (inj₁ (_ , p⟶p′ , refl)))
    lemma′ refl = refl

    lemma″ :
      ∀ {q′₂ x} (q′₁≡q′₂ : proj₁ (lr₁ p⟶p′) ≡ q′₂) →
      ([ i ] f₁ (inj₁ (μ , p⟶p′ , refl)) ≡′
             subst (ν′ S̲t̲e̲p̲ ∞ ∘ (p′ ,_)) (sym q′₁≡q′₂) x)
        ≡
      ([ i ] subst (ν′ S̲t̲e̲p̲ ∞ ∘ (p′ ,_)) q′₁≡q′₂
                   (f₁ (inj₁ (_ , p⟶p′ , refl))) ≡′ x)
    lemma″ refl = refl

  lemma₅₂ :
    ∀ {q′ μ} {q⟶q′ : q [ μ ]⟶ q′}
    (p′₁≡p′₂ : proj₁ (rl₁ q⟶q′) ≡ proj₁ (rl₂ q⟶q′)) →
    ([ i ] f₁ (inj₂ (μ , q⟶q′ , refl)) ≡′
           f₂ (inj₂ (μ , q⟶q′ , sym p′₁≡p′₂)))
      ≡
    ([ i ] subst (ν′ S̲t̲e̲p̲ ∞ ∘ (_, q′)) p′₁≡p′₂
                 (f₁ (inj₂ (_ , q⟶q′ , refl))) ≡′
           f₂ (inj₂ (_ , q⟶q′ , refl)))
  lemma₅₂ {q′} {μ} {q⟶q′} p′₁≡p′₂ =
    ([ i ] f₁ (inj₂ (μ , q⟶q′ , refl)) ≡′
           f₂ (inj₂ (μ , q⟶q′ , sym p′₁≡p′₂)))        ≡⟨ cong ([ _ ] f₁ _ ≡′_) $ lemma′ p′₁≡p′₂ ⟩

    ([ i ] f₁ (inj₂ (μ , q⟶q′ , refl)) ≡′
           subst (ν′ S̲t̲e̲p̲ ∞ ∘ (_, q′)) (sym p′₁≡p′₂)
                 (f₂ (inj₂ (_ , q⟶q′ , refl))))       ≡⟨ lemma″ p′₁≡p′₂ ⟩∎

    ([ i ] subst (ν′ S̲t̲e̲p̲ ∞ ∘ (_, q′)) p′₁≡p′₂
                 (f₁ (inj₂ (_ , q⟶q′ , refl))) ≡′
           f₂ (inj₂ (_ , q⟶q′ , refl)))               ∎
    where
    lemma′ :
      ∀ {q′₁} (p′₁≡p′₂ : q′₁ ≡ proj₁ (rl₂ q⟶q′)) →
      f₂ (inj₂ (μ , q⟶q′ , sym p′₁≡p′₂))
        ≡
      subst (ν′ S̲t̲e̲p̲ ∞ ∘ (_, q′)) (sym p′₁≡p′₂)
            (f₂ (inj₂ (_ , q⟶q′ , refl)))
    lemma′ refl = refl

    lemma″ :
      ∀ {q′₂ x} (p′₁≡p′₂ : proj₁ (rl₁ q⟶q′) ≡ q′₂) →
      ([ i ] f₁ (inj₂ (μ , q⟶q′ , refl)) ≡′
             subst (ν′ S̲t̲e̲p̲ ∞ ∘ (_, q′)) (sym p′₁≡p′₂) x)
        ≡
      ([ i ] subst (ν′ S̲t̲e̲p̲ ∞ ∘ (_, q′)) p′₁≡p′₂
                   (f₁ (inj₂ (_ , q⟶q′ , refl))) ≡′ x)
    lemma″ refl = refl

module Bisimilarity-of-∼
         {p q} {i : Size}
         (p∼q₁ p∼q₂ : ν S̲t̲e̲p̲ ∞ (p , q))
         where

  -- A "constructor".

  ⟨_,_,_,_⟩ :
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
  ⟨_,_,_,_⟩ = curry (_↔_.from ([]≡↔ p∼q₁ p∼q₂))

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
  left-to-right = proj₁ ∘ _↔_.to ([]≡↔ p∼q₁ p∼q₂)

  right-to-left :
    [ i ] p∼q₁ ≡ p∼q₂ →
    ∀ {q′ μ} (q⟶q′ : q [ μ ]⟶ q′) →
    let p′₁ , p⟶p′₁ , p′∼q′₁ = S̲t̲e̲p̲.right-to-left p∼q₁ q⟶q′
        p′₂ , p⟶p′₂ , p′∼q′₂ = S̲t̲e̲p̲.right-to-left p∼q₂ q⟶q′
    in ∃ λ (p′₁≡p′₂ : p′₁ ≡ p′₂) →
         subst (p [ μ ]↝₂_) p′₁≡p′₂ p⟶p′₁ ≡ p⟶p′₂
           ×
         [ i ] subst (ν′ S̲t̲e̲p̲ ∞ ∘ (_, q′)) p′₁≡p′₂ p′∼q′₁ ≡′ p′∼q′₂
  right-to-left = proj₂ ∘ _↔_.to ([]≡↔ p∼q₁ p∼q₂)

-- A statement of extensionality for bisimilarity.

Extensionality : Set
Extensionality = ν′-extensionality S̲t̲e̲p̲

-- This form of extensionality can be used to derive another form.

extensionality :
  Extensionality →
  ∀ {p q} {p∼q₁ p∼q₂ : ν S̲t̲e̲p̲ ∞ (p , q)} →
  [ ∞ ] p∼q₁ ≡ p∼q₂ → p∼q₁ ≡ p∼q₂
extensionality ext = ν-extensionality ext

open S̲t̲e̲p̲ public using (⟨_,_⟩; left-to-right; right-to-left)
