------------------------------------------------------------------------
-- The one-sided Step function, used to define similarity and the
-- two-sided Step function
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Labelled-transition-system

module Similarity.Step
         {ℓ}
         (lts : LTS ℓ)
         (open LTS lts)
         (_[_]↝_ : Proc → Label → Proc → Set ℓ)
         where

open import Equality.Propositional
open import Logical-equivalence using (_⇔_)
open import Prelude

open import Bijection equality-with-J as Bijection using (_↔_)
import Equivalence equality-with-J as Eq
open import Function-universe equality-with-J as F hiding (id; _∘_)
open import H-level equality-with-J
open import H-level.Closure equality-with-J

open import Indexed-container hiding (⟨_⟩)
open import Relation

private
 module Temporarily-private where

  -- If _[_]↝_ is instantiated with _[_]⟶_, then this is basically the
  -- function s from Section 6.3.4.2 in Pous and Sangiorgi's
  -- "Enhancements of the bisimulation proof method", except that
  -- clause (3) is omitted.
  --
  -- Similarly, if _[_]↝_ is instantiated with _[_]⇒̂_, then this is
  -- basically the function w from Section 6.5.2.4, except that
  -- "P R Q" is omitted.

  record Step {r} (R : Rel₂ r Proc) (pq : Proc × Proc) :
              Set (ℓ ⊔ r) where
    constructor ⟨_⟩

    private
      p = proj₁ pq
      q = proj₂ pq

    field
      challenge : ∀ {p′ μ} →
                  p [ μ ]⟶ p′ → ∃ λ q′ → q [ μ ]↝ q′ × R (p′ , q′)

open Temporarily-private using (Step)

-- Used to aid type inference. Note that this type is parametrised
-- (see the module telescope above). The inclusion of a value of this
-- type in the definition of StepC below makes it easier for Agda to
-- infer the LTS parameter from the types ν StepC i (p , q) and
-- ν′ StepC i (p , q).

record Magic : Set where

-- The Magic type is isomorphic to the unit type.

Magic↔⊤ : Magic ↔ ⊤
Magic↔⊤ = record
  { surjection = record
    { right-inverse-of = λ _ → refl
    }
  ; left-inverse-of = λ _ → refl
  }

-- The Step function, expressed as an indexed container.

StepC : Container (Proc × Proc) (Proc × Proc)
StepC =
  (λ { (p , q) → Magic  -- Included in order to aid type inference.
                   ×
                 (∀ {p′ μ} → p [ μ ]⟶ p′ → ∃ λ q′ → q [ μ ]↝ q′)
     })
    ◁
  (λ { {o = p , q} (_ , lr) (p′ , q′) →
       ∃ λ μ → ∃ λ (p⟶p′ : p [ μ ]⟶ p′) → proj₁ (lr p⟶p′) ≡ q′
     })

-- The definition of Step in terms of a container is pointwise
-- logically equivalent to the direct definition, and in the presence
-- of extensionality it is pointwise isomorphic to the direct
-- definition.

Step↔StepC :
  ∀ {k r} {R : Rel₂ r Proc} {pq} →
  Extensionality? k ℓ (ℓ ⊔ r) →
  Step R pq ↝[ k ] ⟦ StepC ⟧ R pq
Step↔StepC {r = r} {R} {pq} = generalise-ext? Step⇔StepC λ ext → record
  { surjection = record
    { logical-equivalence = Step⇔StepC
    ; right-inverse-of    = λ where
        (_ , f) →
          Σ-≡,≡→≡ refl $
            implicit-extensionality ext λ _ →
            apply-ext (lower-extensionality lzero ℓ ext) $
              to₂∘from f
    }
  ; left-inverse-of = λ _ → refl
  }
  where
  to₁ : Step R pq → Container.Shape StepC pq
  to₁ Step.⟨ lr ⟩ =
      _
    , (λ p⟶p′ → Σ-map id proj₁ (lr p⟶p′))

  to₂ :
    (s : Step R pq) →
    Container.Position StepC (to₁ s) ⊆ R
  to₂ Step.⟨ lr ⟩ (_ , p⟶p′ , refl) = proj₂ (proj₂ (lr p⟶p′))

  from : ⟦ StepC ⟧ R pq → Step R pq
  from ((_ , lr) , f) =
    Step.⟨ (λ p⟶p′ →
              let q′ , q⟶q′ = lr p⟶p′
              in  q′ , q⟶q′ , f (_ , p⟶p′ , refl))
         ⟩

  Step⇔StepC : Step R pq ⇔ ⟦ StepC ⟧ R pq
  Step⇔StepC = record
    { to   = λ s → to₁ s , to₂ s
    ; from = from
    }

  to₂∘from :
    ∀ {p′q′} {s : Container.Shape StepC pq}
    (f : Container.Position StepC s ⊆ R) →
    (pos : Container.Position StepC s p′q′) →
    proj₂ (_⇔_.to Step⇔StepC (_⇔_.from Step⇔StepC (s , f))) pos ≡ f pos
  to₂∘from f (_ , _ , refl) = refl

module StepC {r} {R : Rel₂ r Proc} {p q} where

  -- A "constructor".

  ⟨_⟩ :
    (∀ {p′ μ} → p [ μ ]⟶ p′ → ∃ λ q′ → q [ μ ]↝ q′ × R (p′ , q′)) →
    ⟦ StepC ⟧ R (p , q)
  ⟨ lr ⟩ = _⇔_.to (Step↔StepC _) Step.⟨ lr ⟩

  -- A "projection".

  challenge :
    ⟦ StepC ⟧ R (p , q) →
    ∀ {p′ μ} → p [ μ ]⟶ p′ → ∃ λ q′ → q [ μ ]↝ q′ × R (p′ , q′)
  challenge = Step.challenge ∘ _⇔_.from (Step↔StepC _)

open Temporarily-private public

-- An unfolding lemma for ⟦ StepC ⟧₂.

⟦StepC⟧₂↔ :
  ∀ {x} {X : Rel₂ x Proc} →
  Extensionality ℓ ℓ →
  (R : ∀ {o} → Rel₂ ℓ (X o)) →
  ∀ {p q} (p∼q₁ p∼q₂ : ⟦ StepC ⟧ X (p , q)) →

  ⟦ StepC ⟧₂ R (p∼q₁ , p∼q₂)

    ↔

  (∀ {p′ μ} (p⟶p′ : p [ μ ]⟶ p′) →
   let q′₁ , q⟶q′₁ , p′≤q′₁ = StepC.challenge p∼q₁ p⟶p′
       q′₂ , q⟶q′₂ , p′≤q′₂ = StepC.challenge p∼q₂ p⟶p′
   in ∃ λ (q′₁≡q′₂ : q′₁ ≡ q′₂) →
        subst (q [ μ ]↝_) q′₁≡q′₂ q⟶q′₁ ≡ q⟶q′₂
          ×
        R (subst (X ∘ (p′ ,_)) q′₁≡q′₂ p′≤q′₁ , p′≤q′₂))

⟦StepC⟧₂↔ {X = X} ext R {p} {q}
          (s₁@(_ , ch₁) , f₁) (s₂@(_ , ch₂) , f₂) =

  (∃ λ (eq : s₁ ≡ s₂) →
   ∀ {o} (p : Container.Position StepC s₁ o) →
   R (f₁ p , f₂ (subst (λ s → Container.Position StepC s o) eq p)))    ↝⟨ inverse $ Σ-cong ≡×≡↔≡ (λ _ → F.id) ⟩

  (∃ λ (eq : proj₁ s₁ ≡ proj₁ s₂ × (λ {_ _} → ch₁) ≡ ch₂) →
   ∀ {o} (p : Container.Position StepC s₁ o) →
   R (f₁ p , f₂ (subst (λ s → Container.Position StepC s o)
                       (cong₂ _,_ (proj₁ eq) (proj₂ eq)) p)))          ↝⟨ inverse Σ-assoc ⟩

  (∃ λ (eq₁ : proj₁ s₁ ≡ proj₁ s₂) →
   ∃ λ (eq₂ : (λ {_ _} → ch₁) ≡ ch₂) →
   ∀ {o} (p : Container.Position StepC s₁ o) →
   R (f₁ p , f₂ (subst (λ s → Container.Position StepC s o)
                       (cong₂ _,_ eq₁ eq₂) p)))                        ↝⟨ drop-⊤-left-Σ (_⇔_.to contractible⇔↔⊤ $
                                                                          mono₁ 0 (_⇔_.from contractible⇔↔⊤ Magic↔⊤) _ _) ⟩
  (∃ λ (eq : (λ {_ _} → ch₁) ≡ ch₂) →
   ∀ {o} (p : Container.Position StepC s₁ o) →
   R (f₁ p , f₂ (subst (λ s → Container.Position StepC s o)
                       (cong₂ _,_ refl eq) p)))                        ↝⟨ (∃-cong λ eq → implicit-∀-cong ext $ ∀-cong ext λ _ →
                                                                           ≡⇒↝ _ $
                                                                           cong (λ (eq : s₁ ≡ s₂) →
                                                                                   R (f₁ _ ,
                                                                                      f₂ (subst (λ s → Container.Position StepC s _) eq _))) $
                                                                           trans-reflˡ (cong (_ ,_) eq)) ⟩
  (∃ λ (eq : (λ {_ _} → ch₁) ≡ ch₂) →
   ∀ {o} (p : Container.Position StepC s₁ o) →
   R (f₁ p , f₂ (subst (λ s → Container.Position StepC s o)
                       (cong (_ ,_) eq) p)))                           ↝⟨ (∃-cong λ eq → implicit-∀-cong ext λ {o} → ∀-cong ext λ p →
                                                                           ≡⇒↝ _ $ cong (λ p → R {o = o} (f₁ _ , f₂ p)) $ sym $
                                                                           subst-∘ (λ (s : Container.Shape StepC _) → Container.Position StepC s o)
                                                                                   _ eq) ⟩
  (∃ λ (eq : (λ {_ _} → ch₁) ≡ ch₂) →
   ∀ {o} (p : Container.Position StepC s₁ o) →
   R (f₁ p , f₂ (subst (λ (ch : ∀ {_ _} → _) →
                          Container.Position StepC (_ , ch) o)
                       eq p)))                                         ↔⟨⟩

  (∃ λ (eq : _≡_ {A = ∀ {p′ μ} → _} ch₁ ch₂) →
   ∀ {p′q′} →
   (pos : ∃ λ μ → ∃ λ (p⟶p′ : p [ μ ]⟶ proj₁ p′q′) →
          proj₁ (ch₁ p⟶p′) ≡ proj₂ p′q′) →
   R (f₁ pos ,
      f₂ (subst (λ ch → ∃ λ μ → ∃ λ (p⟶p′ : p [ μ ]⟶ proj₁ p′q′) →
                        proj₁ (ch p⟶p′) ≡ proj₂ p′q′)
                eq pos)))                                              ↝⟨ (∃-cong λ _ → Bijection.implicit-Π↔Π) ⟩

  (∃ λ (eq : _≡_ {A = ∀ {p′ μ} → _} ch₁ ch₂) →
   ∀ p′q′ →
   (pos : ∃ λ μ → ∃ λ (p⟶p′ : p [ μ ]⟶ proj₁ p′q′) →
          proj₁ (ch₁ p⟶p′) ≡ proj₂ p′q′) →
   R (f₁ pos ,
      f₂ (subst (λ ch → ∃ λ μ → ∃ λ (p⟶p′ : p [ μ ]⟶ proj₁ p′q′) →
                        proj₁ (ch p⟶p′) ≡ proj₂ p′q′)
                eq pos)))                                              ↝⟨ (∃-cong λ _ → currying) ⟩

  (∃ λ (eq : _≡_ {A = ∀ {p′ μ} → _} ch₁ ch₂) →
   ∀ p′ q′ →
   (pos : ∃ λ μ → ∃ λ (p⟶p′ : p [ μ ]⟶ p′) → proj₁ (ch₁ p⟶p′) ≡ q′) →
   R (f₁ pos ,
      f₂ (subst (λ ch → ∃ λ μ → ∃ λ (p⟶p′ : p [ μ ]⟶ p′) →
                        proj₁ (ch p⟶p′) ≡ q′)
                eq pos)))                                              ↝⟨ (∃-cong λ _ → ∀-cong ext λ _ → ∀-cong ext λ _ → currying) ⟩

  (∃ λ (eq : _≡_ {A = ∀ {p′ μ} → _} ch₁ ch₂) →
   ∀ p′ q′ μ →
   (pos : ∃ λ (p⟶p′ : p [ μ ]⟶ p′) → proj₁ (ch₁ p⟶p′) ≡ q′) →
   R (f₁ (μ , pos) ,
      f₂ (subst (λ ch → ∃ λ μ → ∃ λ (p⟶p′ : p [ μ ]⟶ p′) →
                        proj₁ (ch p⟶p′) ≡ q′)
                eq (μ , pos))))                                        ↝⟨ (∃-cong λ _ → ∀-cong ext λ _ → ∀-cong ext λ _ → ∀-cong ext λ _ →
                                                                           currying) ⟩
  (∃ λ (eq : _≡_ {A = ∀ {p′ μ} → _} ch₁ ch₂) →
   ∀ p′ q′ μ (p⟶p′ : p [ μ ]⟶ p′) (≡q′ : proj₁ (ch₁ p⟶p′) ≡ q′) →
   R (f₁ (μ , p⟶p′ , ≡q′) ,
      f₂ (subst (λ ch → ∃ λ μ → ∃ λ (p⟶p′ : p [ μ ]⟶ p′) →
                        proj₁ (ch p⟶p′) ≡ q′)
                eq (μ , p⟶p′ , ≡q′))))                                 ↝⟨ (∃-cong λ _ → ∀-cong ext λ _ → Π-comm) ⟩

  (∃ λ (eq : _≡_ {A = ∀ {p′ μ} → _} ch₁ ch₂) →
   ∀ p′ μ q′ (p⟶p′ : p [ μ ]⟶ p′) (≡q′ : proj₁ (ch₁ p⟶p′) ≡ q′) →
   R (f₁ (μ , p⟶p′ , ≡q′) ,
      f₂ (subst (λ ch → ∃ λ μ → ∃ λ (p⟶p′ : p [ μ ]⟶ p′) →
                        proj₁ (ch p⟶p′) ≡ q′)
                eq (μ , p⟶p′ , ≡q′))))                                 ↝⟨ (∃-cong λ _ → ∀-cong ext λ _ → ∀-cong ext λ _ → Π-comm) ⟩

  (∃ λ (eq : _≡_ {A = ∀ {p′ μ} → _} ch₁ ch₂) →
   ∀ p′ μ (p⟶p′ : p [ μ ]⟶ p′) q′ (≡q′ : proj₁ (ch₁ p⟶p′) ≡ q′) →
   R (f₁ (μ , p⟶p′ , ≡q′) ,
      f₂ (subst (λ ch → ∃ λ μ → ∃ λ (p⟶p′ : p [ μ ]⟶ p′) →
                        proj₁ (ch p⟶p′) ≡ q′)
                eq (μ , p⟶p′ , ≡q′))))                                 ↝⟨ (∃-cong λ _ → ∀-cong ext λ _ → ∀-cong ext λ _ → ∀-cong ext λ _ →
                                                                              inverse $ ∀-intro ext _) ⟩
  (∃ λ (eq : _≡_ {A = ∀ {p′ μ} → _} ch₁ ch₂) →
   ∀ p′ μ (p⟶p′ : p [ μ ]⟶ p′) →
   R (f₁ (μ , p⟶p′ , refl) ,
      f₂ (subst (λ ch → ∃ λ μ → ∃ λ (p⟶p′′ : p [ μ ]⟶ p′) →
                        proj₁ (ch p⟶p′′) ≡ proj₁ (ch₁ p⟶p′))
                eq (μ , p⟶p′ , refl))))                                ↝⟨ (∃-cong λ eq → ∀-cong ext λ _ → ∀-cong ext λ _ → ∀-cong ext λ _ →
                                                                           ≡⇒↝ _ $ cong (R ∘ (f₁ _ ,_) ∘ f₂) $ lemma₁ eq) ⟩
  (∃ λ (eq : _≡_ {A = ∀ {p′ μ} → _} ch₁ ch₂) →
   ∀ p′ μ (p⟶p′ : p [ μ ]⟶ p′) →
   R (f₁ (μ , p⟶p′ , refl) ,
      f₂ (μ , p⟶p′ , sym (cong (λ ch → proj₁ (ch p⟶p′)) eq))))         ↝⟨ (∃-cong λ eq → ∀-cong ext λ _ → inverse Bijection.implicit-Π↔Π) ⟩

  (∃ λ (eq : _≡_ {A = ∀ {p′ μ} → _} ch₁ ch₂) →
   ∀ p′ {μ} (p⟶p′ : p [ μ ]⟶ p′) →
   R (f₁ (μ , p⟶p′ , refl) ,
      f₂ (μ , p⟶p′ , sym (cong (λ ch → proj₁ (ch p⟶p′)) eq))))         ↝⟨ (∃-cong λ eq → inverse Bijection.implicit-Π↔Π) ⟩

  (∃ λ (eq : _≡_ {A = ∀ {p′ μ} → _} ch₁ ch₂) →
   ∀ {p′ μ} (p⟶p′ : p [ μ ]⟶ p′) →
   R (f₁ (μ , p⟶p′ , refl) ,
      f₂ (μ , p⟶p′ , sym (cong (λ ch → proj₁ (ch p⟶p′)) eq))))         ↝⟨ (Σ-cong (inverse $ implicit-extensionality-isomorphism
                                                                                               {k = bijection} ext) λ eq →
                                                                           implicit-∀-cong ext $ implicit-∀-cong ext $ ∀-cong ext λ p⟶p′ →
                                                                           ≡⇒↝ _ $ sym $ cong (λ eq →
                                                                             R (f₁ _ , f₂ (_ , p⟶p′ , sym (cong (λ ch → proj₁ (ch p⟶p′)) eq)))) $
                                                                           _↔_.right-inverse-of (implicit-extensionality-isomorphism ext) eq) ⟩
  (∃ λ (eq : ∀ p′ → (λ {μ} → ch₁ {p′ = p′} {μ = μ}) ≡ ch₂) →
   let eq′ = _↔_.to (implicit-extensionality-isomorphism ext) eq in
   ∀ {p′ μ} (p⟶p′ : p [ μ ]⟶ p′) →
   R (f₁ (μ , p⟶p′ , refl) ,
      f₂ (μ , p⟶p′ , sym (cong (λ ch → proj₁ (ch p⟶p′)) eq′))))        ↝⟨ (∃-cong λ eq →
                                                                           implicit-∀-cong ext $ implicit-∀-cong ext $ ∀-cong ext λ p⟶p′ →
                                                                           ≡⇒↝ _ $ cong (λ eq → R (f₁ _ , f₂ (_ , p⟶p′ , sym eq))) $
                                                                           lemma₂ eq) ⟩
  (∃ λ (eq : ∀ p′ → (λ {μ} → ch₁ {p′ = p′} {μ = μ}) ≡ ch₂) →
   ∀ {p′ μ} (p⟶p′ : p [ μ ]⟶ p′) →
   R (f₁ (μ , p⟶p′ , refl) ,
      f₂ (μ , p⟶p′ , sym (cong (λ ch → proj₁ (ch p′ p⟶p′))
                               (apply-ext (Eq.good-ext ext) eq)))))    ↝⟨ (Σ-cong (inverse $ ∀-cong ext λ _ →
                                                                                   implicit-extensionality-isomorphism
                                                                                     {k = bijection} ext) λ eq →
                                                                           implicit-∀-cong ext $ implicit-∀-cong ext $ ∀-cong ext λ p⟶p′ →
                                                                           ≡⇒↝ _ $ sym $ cong (λ eq →
                                                                             R (f₁ _ , f₂ (_ , p⟶p′ , sym (cong (λ ch → proj₁ (ch _ p⟶p′))
                                                                                                             (apply-ext (Eq.good-ext ext) eq))))) $
                                                                           apply-ext ext $
                                                                           _↔_.right-inverse-of (implicit-extensionality-isomorphism ext) ∘ eq) ⟩
  (∃ λ (eq : ∀ p′ μ → ch₁ {p′ = p′} {μ = μ} ≡ ch₂) →
   let eq′ = implicit-extensionality (Eq.good-ext ext) ∘ eq in
   ∀ {p′ μ} (p⟶p′ : p [ μ ]⟶ p′) →
   R (f₁ (μ , p⟶p′ , refl) ,
      f₂ (μ , p⟶p′ , sym (cong (λ ch → proj₁ (ch p′ p⟶p′))
                               (apply-ext (Eq.good-ext ext) eq′)))))   ↝⟨ (∃-cong λ _ →
                                                                           implicit-∀-cong ext $ implicit-∀-cong ext $ ∀-cong ext λ _ →
                                                                           ≡⇒↝ _ $ cong (λ eq → R (f₁ _ , f₂ (_ , _ , sym eq))) $
                                                                           lemma₃ _) ⟩
  (∃ λ (eq : ∀ p′ μ → ch₁ {p′ = p′} {μ = μ} ≡ ch₂) →
   ∀ {p′ μ} (p⟶p′ : p [ μ ]⟶ p′) →
   R (f₁ (μ , p⟶p′ , refl) ,
      f₂ (μ , p⟶p′ , sym (cong (λ ch → proj₁ (ch p⟶p′)) (eq p′ μ)))))  ↝⟨ Σ-cong (inverse Bijection.implicit-Π↔Π) (λ _ → F.id) ⟩

  (∃ λ (eq : ∀ {p′} μ → ch₁ {p′ = p′} {μ = μ} ≡ ch₂) →
   ∀ {p′ μ} (p⟶p′ : p [ μ ]⟶ p′) →
   R (f₁ (μ , p⟶p′ , refl) ,
      f₂ (μ , p⟶p′ , sym (cong (λ ch → proj₁ (ch p⟶p′)) (eq μ)))))     ↝⟨ Σ-cong (implicit-∀-cong ext $ inverse Bijection.implicit-Π↔Π)
                                                                                 (λ _ → F.id) ⟩
  (∃ λ (eq : ∀ {p′ μ} → ch₁ {p′ = p′} {μ = μ} ≡ ch₂) →
   ∀ {p′ μ} (p⟶p′ : p [ μ ]⟶ p′) →
   R (f₁ (μ , p⟶p′ , refl) ,
      f₂ (μ , p⟶p′ , sym (cong (λ ch → proj₁ (ch p⟶p′)) eq))))         ↝⟨ (∃-cong λ eq →
                                                                           implicit-∀-cong ext $ implicit-∀-cong ext $ ∀-cong ext λ p⟶p′ →
                                                                           ≡⇒↝ _ $ cong (λ eq → R (f₁ _ , f₂ (_ , _ , sym eq))) $ sym $
                                                                           cong-∘ proj₁ (_$ p⟶p′) (eq {μ = _})) ⟩
  (∃ λ (eq : ∀ {p′ μ} → ch₁ {p′ = p′} {μ = μ} ≡ ch₂) →
   ∀ {p′ μ} (p⟶p′ : p [ μ ]⟶ p′) →
   R (f₁ (μ , p⟶p′ , refl) ,
      f₂ (μ , p⟶p′ , sym (cong proj₁ $ cong (_$ p⟶p′) eq))))           ↝⟨ Σ-cong (implicit-∀-cong ext $ implicit-∀-cong ext $ inverse $
                                                                                  Eq.extensionality-isomorphism ext)
                                                                                 (λ _ → F.id) ⟩
  (∃ λ (eq : ∀ {p′ μ} (p⟶p′ : p [ μ ]⟶ p′) → ch₁ p⟶p′ ≡ ch₂ p⟶p′) →
   ∀ {p′ μ} (p⟶p′ : p [ μ ]⟶ p′) →
   R (f₁ (μ , p⟶p′ , refl) ,
      f₂ (μ , p⟶p′ , sym (cong proj₁ (eq p⟶p′)))))                     ↝⟨ inverse implicit-ΠΣ-comm ⟩

  (∀ {p′} →
   ∃ λ (eq : ∀ {μ} (p⟶p′ : p [ μ ]⟶ p′) → ch₁ p⟶p′ ≡ ch₂ p⟶p′) →
   ∀ {μ} (p⟶p′ : p [ μ ]⟶ p′) →
   R (f₁ (μ , p⟶p′ , refl) ,
      f₂ (μ , p⟶p′ , sym (cong proj₁ (eq p⟶p′)))))                     ↝⟨ implicit-∀-cong ext $ inverse implicit-ΠΣ-comm ⟩

  (∀ {p′ μ} →
   ∃ λ (eq : (p⟶p′ : p [ μ ]⟶ p′) → ch₁ p⟶p′ ≡ ch₂ p⟶p′) →
   ∀ p⟶p′ → R (f₁ (μ , p⟶p′ , refl) ,
               f₂ (μ , p⟶p′ , sym (cong proj₁ (eq p⟶p′)))))            ↝⟨ implicit-∀-cong ext $ implicit-∀-cong ext $ inverse ΠΣ-comm ⟩

  (∀ {p′ μ} (p⟶p′ : p [ μ ]⟶ p′) →
   ∃ λ (eq : ch₁ p⟶p′ ≡ ch₂ p⟶p′) →
   R (f₁ (μ , p⟶p′ , refl) , f₂ (μ , p⟶p′ , sym (cong proj₁ eq))))     ↝⟨ (inverse $ implicit-∀-cong ext $ implicit-∀-cong ext $ ∀-cong ext λ _ →
                                                                           Σ-cong Bijection.Σ-≡,≡↔≡ λ _ → F.id) ⟩
  (∀ {p′ μ} (p⟶p′ : p [ μ ]⟶ p′) →
   let q′₁ , q⟶q′₁ = ch₁ p⟶p′
       q′₂ , q⟶q′₂ = ch₂ p⟶p′
   in ∃ λ (eq : ∃ λ (q′₁≡q′₂ : q′₁ ≡ q′₂) →
                  subst (q [ μ ]↝_) q′₁≡q′₂ q⟶q′₁ ≡ q⟶q′₂) →
      R (f₁ (μ , p⟶p′ , refl) ,
         f₂ (μ , p⟶p′ , sym (cong proj₁ (uncurry Σ-≡,≡→≡ eq)))))       ↝⟨ (implicit-∀-cong ext $ implicit-∀-cong ext $ ∀-cong ext λ _ →
                                                                           ∃-cong λ eq →
                                                                           ≡⇒↝ _ $ cong (λ eq → R (f₁ _ , f₂ (_ , _ , sym eq))) $
                                                                           proj₁-Σ-≡,≡→≡ (proj₁ eq) (proj₂ eq)) ⟩
  (∀ {p′ μ} (p⟶p′ : p [ μ ]⟶ p′) →
   let q′₁ , q⟶q′₁ = ch₁ p⟶p′
       q′₂ , q⟶q′₂ = ch₂ p⟶p′
   in ∃ λ (eq : ∃ λ (q′₁≡q′₂ : q′₁ ≡ q′₂) →
                  subst (q [ μ ]↝_) q′₁≡q′₂ q⟶q′₁ ≡ q⟶q′₂) →
      R (f₁ (μ , p⟶p′ , refl) , f₂ (μ , p⟶p′ , sym (proj₁ eq))))       ↝⟨ (implicit-∀-cong ext $ implicit-∀-cong ext $ ∀-cong ext λ _ →
                                                                           inverse Σ-assoc) ⟩
  (∀ {p′ μ} (p⟶p′ : p [ μ ]⟶ p′) →
   let q′₁ , q⟶q′₁ = ch₁ p⟶p′
       q′₂ , q⟶q′₂ = ch₂ p⟶p′
   in ∃ λ (q′₁≡q′₂ : q′₁ ≡ q′₂) →
        subst (q [ μ ]↝_) q′₁≡q′₂ q⟶q′₁ ≡ q⟶q′₂
          ×
        R (f₁ (μ , p⟶p′ , refl) , f₂ (μ , p⟶p′ , sym q′₁≡q′₂)))        ↝⟨ (implicit-∀-cong ext $ implicit-∀-cong ext $ ∀-cong ext λ p⟶p′ →
                                                                           ∃-cong λ q′₁≡q′₂ → ∃-cong λ _ → ≡⇒↝ _ $
                                                                           lemma₄ q′₁≡q′₂) ⟩
  (∀ {p′ μ} (p⟶p′ : p [ μ ]⟶ p′) →
   let q′₁ , q⟶q′₁ = ch₁ p⟶p′
       q′₂ , q⟶q′₂ = ch₂ p⟶p′
   in ∃ λ (q′₁≡q′₂ : q′₁ ≡ q′₂) →
        subst (q [ μ ]↝_) q′₁≡q′₂ q⟶q′₁ ≡ q⟶q′₂
          ×
        R (subst (X ∘ (p′ ,_)) q′₁≡q′₂ (f₁ (_ , p⟶p′ , refl)) ,
           f₂ (_ , p⟶p′ , refl)))                                      ↔⟨⟩

  (∀ {p′ μ} (p⟶p′ : p [ μ ]⟶ p′) →
   let q′₁ , q⟶q′₁ , p′≤q′₁ = StepC.challenge (s₁ , f₁) p⟶p′
       q′₂ , q⟶q′₂ , p′≤q′₂ = StepC.challenge (s₂ , f₂) p⟶p′
   in ∃ λ (q′₁≡q′₂ : q′₁ ≡ q′₂) →
        subst (q [ μ ]↝_) q′₁≡q′₂ q⟶q′₁ ≡ q⟶q′₂
          ×
        R (subst (X ∘ (p′ ,_)) q′₁≡q′₂ p′≤q′₁ , p′≤q′₂))               □

  where

  lemma₁ = λ {p q} {f g : ∀ {p′ μ} → p [ μ ]⟶ p′ → ∃ (q [ μ ]↝_)}
             (eq : (λ {p′ μ} → f {p′ = p′} {μ = μ}) ≡ g)
             {p′ μ} {p⟶p′ : p [ μ ]⟶ p′} →

    subst (λ ch →
             ∃ λ μ → ∃ λ (p⟶p′′ : p [ μ ]⟶ p′) →
             proj₁ (ch p⟶p′′) ≡ proj₁ (f p⟶p′))
          eq (μ , p⟶p′ , refl)                          ≡⟨ push-subst-pair′ {y≡z = eq} _ _ _ ⟩

    ( μ
    , subst₂ (λ { (ch , μ) →
                  ∃ λ (p⟶p′′ : p [ μ ]⟶ p′) →
                  proj₁ (ch p⟶p′′) ≡ proj₁ (f p⟶p′) })
             eq (subst-const eq) (p⟶p′ , refl)
    )                                                   ≡⟨ cong (μ ,_) $
                                                           cong (λ eq → subst (λ { (ch , μ) →
                                                                                   ∃ λ (p⟶p′′ : p [ μ ]⟶ p′) →
                                                                                   proj₁ (ch p⟶p′′) ≡ proj₁ (f p⟶p′) })
                                                                              eq (p⟶p′ , refl)) $
                                                           Σ-≡,≡→≡-subst-const eq refl ⟩
    ( μ
    , subst (λ { (ch , μ) →
                 ∃ λ (p⟶p′′ : p [ μ ]⟶ p′) →
                 proj₁ (ch p⟶p′′) ≡ proj₁ (f p⟶p′) })
            (cong₂ _,_ eq refl) (p⟶p′ , refl)
    )                                                   ≡⟨⟩

    ( μ
    , subst (λ { (ch , μ) →
                 ∃ λ (p⟶p′′ : p [ μ ]⟶ p′) →
                 proj₁ (ch p⟶p′′) ≡ proj₁ (f p⟶p′) })
            (cong (_, _) eq) (p⟶p′ , refl)
    )                                                   ≡⟨ cong (μ ,_) $ sym $
                                                           subst-∘ _ _ eq ⟩
    ( μ
    , subst (λ ch →
               ∃ λ (p⟶p′′ : p [ μ ]⟶ p′) →
               proj₁ (ch p⟶p′′) ≡ proj₁ (f p⟶p′))
            eq (p⟶p′ , refl)
    )                                                   ≡⟨ cong (μ ,_) $
                                                           push-subst-pair′ {y≡z = eq} _ _ _ ⟩
    ( μ
    , p⟶p′
    , subst₂ (λ { (ch , p⟶p′′) →
                  proj₁ (ch p⟶p′′) ≡ proj₁ (f p⟶p′) })
             eq (subst-const eq) refl
    )                                                   ≡⟨ cong (λ eq → (_ , p⟶p′ , subst (λ { (ch , p⟶p′′) → proj₁ (ch p⟶p′′) ≡ proj₁ (f p⟶p′) })
                                                                                          eq refl)) $
                                                           Σ-≡,≡→≡-subst-const eq refl ⟩
    ( μ
    , p⟶p′
    , subst (λ { (ch , p⟶p′′) →
                 proj₁ (ch p⟶p′′) ≡ proj₁ (f p⟶p′) })
            (cong (_, _) eq) refl
    )                                                   ≡⟨ cong (λ eq → (_ , p⟶p′ , eq)) $ sym $
                                                           subst-∘ _ _ eq ⟩
    ( μ
    , p⟶p′
    , subst (λ ch → proj₁ (ch p⟶p′) ≡ proj₁ (f p⟶p′))
            eq refl
    )                                                   ≡⟨ cong (λ eq → (_ , p⟶p′ , eq)) $
                                                           subst-∘ _ _ eq ⟩
    ( μ
    , p⟶p′
    , subst (_≡ proj₁ (f p⟶p′))
            (cong (λ ch → proj₁ (ch p⟶p′)) eq) refl
    )                                                   ≡⟨ cong (λ eq → (_ , p⟶p′ , subst (_≡ _) eq refl)) $
                                                           sym $ sym-sym (cong (λ ch → proj₁ (ch p⟶p′)) eq) ⟩
    ( μ
    , p⟶p′
    , subst (_≡ proj₁ (f p⟶p′))
            (sym $ sym $
               cong (λ ch → proj₁ (ch p⟶p′)) eq)
            refl
    )                                                   ≡⟨ cong (λ eq → (_ , p⟶p′ , eq)) $
                                                           subst-trans (sym $ cong (λ ch → proj₁ (ch p⟶p′)) eq) ⟩∎
    ( μ
    , p⟶p′
    , sym (cong (λ ch → proj₁ (ch p⟶p′)) eq)
    )                                                   ∎

  lemma₂ = λ {p q} {f g : ∀ {p′ μ} → p [ μ ]⟶ p′ → ∃ (q [ μ ]↝_)}
             (eq : ∀ p′ → (λ {μ} → f {p′ = p′} {μ = μ}) ≡ g)
             {p′ μ} {p⟶p′ : p [ μ ]⟶ p′} →

    cong (λ ch → proj₁ (ch p⟶p′))
         (_↔_.to (implicit-extensionality-isomorphism ext) eq)         ≡⟨⟩

    cong (λ ch → proj₁ (ch p⟶p′))
         (implicit-extensionality (Eq.good-ext ext) eq)                ≡⟨ cong-∘ _ _ (apply-ext (Eq.good-ext ext) eq) ⟩∎

    cong (λ ch → proj₁ (ch p′ p⟶p′)) (apply-ext (Eq.good-ext ext) eq)  ∎

  lemma₃ = λ {p q} {f g : ∀ {p′ μ} → p [ μ ]⟶ p′ → ∃ (q [ μ ]↝_)}
             (eq : ∀ p′ μ → f {p′ = p′} {μ = μ} ≡ g)
             {p′ μ p⟶p′} →

    cong (λ (ch : ∀ _ {μ} → _) → proj₁ (ch p′ {μ = μ} p⟶p′))
         (apply-ext (Eq.good-ext ext)
            (implicit-extensionality (Eq.good-ext ext) ∘ eq))             ≡⟨⟩

    cong (λ ch → proj₁ (ch p′ p⟶p′))
         (apply-ext (Eq.good-ext ext)
            (cong (λ f {x} → f x) ∘ (apply-ext (Eq.good-ext ext) ∘ eq)))  ≡⟨ cong (cong (λ ch → proj₁ (ch p′ p⟶p′))) $ sym $
                                                                             Eq.cong-post-∘-good-ext {h = λ f {x} → f x} ext ext
                                                                                                     (apply-ext (Eq.good-ext ext) ∘ eq) ⟩
    cong (λ ch → proj₁ (ch p′ p⟶p′))
         (cong (λ f x {y} → f x y)
               (apply-ext (Eq.good-ext ext)
                  (apply-ext (Eq.good-ext ext) ∘ eq)))                    ≡⟨ cong-∘ _ _ (apply-ext (Eq.good-ext ext)
                                                                                           (apply-ext (Eq.good-ext ext) ∘ eq)) ⟩
    cong (λ ch → proj₁ (ch p′ μ p⟶p′))
         (apply-ext (Eq.good-ext ext)
            (apply-ext (Eq.good-ext ext) ∘ eq))                           ≡⟨ sym $ cong-∘ _ _ (apply-ext (Eq.good-ext ext)
                                                                                                 (apply-ext (Eq.good-ext ext) ∘ eq)) ⟩
    cong (λ ch → proj₁ (ch μ p⟶p′))
         (cong (_$ p′) (apply-ext (Eq.good-ext ext)
                          (apply-ext (Eq.good-ext ext) ∘ eq)))            ≡⟨ cong (cong (λ ch → proj₁ (ch μ p⟶p′))) $ Eq.cong-good-ext ext _ ⟩

    cong (λ ch → proj₁ (ch μ p⟶p′))
         (apply-ext (Eq.good-ext ext) (eq p′))                            ≡⟨ sym $ cong-∘ _ _ (apply-ext (Eq.good-ext ext) (eq p′)) ⟩

    cong (λ ch → proj₁ (ch p⟶p′))
         (cong (_$ μ) (apply-ext (Eq.good-ext ext) (eq p′)))              ≡⟨ cong (cong (λ ch → proj₁ (ch p⟶p′))) $ Eq.cong-good-ext ext _ ⟩∎

    cong (λ ch → proj₁ (ch p⟶p′)) (eq p′ μ)                               ∎

  lemma₄ :
    ∀ {p′ μ} {p⟶p′ : p [ μ ]⟶ p′}
    (q′₁≡q′₂ : proj₁ (ch₁ p⟶p′) ≡ proj₁ (ch₂ p⟶p′)) →
    R (f₁ (μ , p⟶p′ , refl) , f₂ (μ , p⟶p′ , sym q′₁≡q′₂))
      ≡
    R (subst (X ∘ (p′ ,_)) q′₁≡q′₂ (f₁ (_ , p⟶p′ , refl)) ,
       f₂ (_ , p⟶p′ , refl))
  lemma₄ {p′} {μ} {p⟶p′} q′₁≡q′₂ =
    R (f₁ (μ , p⟶p′ , refl) , f₂ (μ , p⟶p′ , sym q′₁≡q′₂))        ≡⟨ cong (R ∘ (f₁ _ ,_)) $ lemma′ q′₁≡q′₂ ⟩

    R (f₁ (μ , p⟶p′ , refl) ,
       subst (X ∘ (p′ ,_)) (sym q′₁≡q′₂) (f₂ (_ , p⟶p′ , refl)))  ≡⟨ lemma″ q′₁≡q′₂ ⟩∎

    R (subst (X ∘ (p′ ,_)) q′₁≡q′₂ (f₁ (_ , p⟶p′ , refl)) ,
       f₂ (_ , p⟶p′ , refl))                                      ∎
    where
    lemma′ :
      ∀ {q′₁} (q′₁≡q′₂ : q′₁ ≡ proj₁ (ch₂ p⟶p′)) →
      f₂ (μ , p⟶p′ , sym q′₁≡q′₂)
        ≡
      subst (X ∘ (p′ ,_)) (sym q′₁≡q′₂) (f₂ (_ , p⟶p′ , refl))
    lemma′ refl = refl

    lemma″ :
      ∀ {q′₂ x} (q′₁≡q′₂ : proj₁ (ch₁ p⟶p′) ≡ q′₂) →
      R (f₁ (μ , p⟶p′ , refl) , subst (X ∘ (p′ ,_)) (sym q′₁≡q′₂) x)
        ≡
      R (subst (X ∘ (p′ ,_)) q′₁≡q′₂ (f₁ (_ , p⟶p′ , refl)) , x)
    lemma″ refl = refl
