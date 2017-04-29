------------------------------------------------------------------------
-- The Step function, used to define bisimilarity
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

open import Labelled-transition-system

module Bisimilarity.Step (lts : LTS) where

open import Equality.Propositional
open import Interval using (ext)
open import Logical-equivalence using (_⇔_)
open import Prelude

open import Bijection equality-with-J using (_↔_)
open import Function-universe equality-with-J hiding (id; _∘_)

open import Bisimilarity.Classical.Preliminaries
open import Indexed-container hiding (⟨_⟩)

open LTS lts

private
 module Temporarily-private where

  -- This is basically the function from Definition 6.3.1 in Pous and
  -- Sangiorgi's "Enhancements of the bisimulation proof method",
  -- except that clause (3) is omitted.

  record Step {r} (_R_ : Rel r Proc) (p q : Proc) : Set r where
    constructor ⟨_,_⟩
    field
      left-to-right : ∀ {p′ μ} →
                      p [ μ ]⟶ p′ → ∃ λ q′ → q [ μ ]⟶ q′ × p′ R q′
      right-to-left : ∀ {q′ μ} →
                      q [ μ ]⟶ q′ → ∃ λ p′ → p [ μ ]⟶ p′ × p′ R q′

open Temporarily-private using (Step)

-- Step is monotone.

Step-monotone : ∀ {ℓ₁ ℓ₂} → Monotone-∀ Step ℓ₁ ℓ₂
Step-monotone R⊆S p q StepRpq =
  Step.⟨ (λ p⟶p′ → Σ-map id (Σ-map id (R⊆S _ _))
                     (Step.left-to-right StepRpq p⟶p′))
       , (λ q⟶q′ → Σ-map id (Σ-map id (R⊆S _ _))
                     (Step.right-to-left StepRpq q⟶q′))
       ⟩

-- Used to aid type inference. Note that this type is parametrised
-- (see the module telescope above). The inclusion of a value of this
-- type in the definition of S̲t̲e̲p̲ below makes it easier for Agda to
-- infer the LTS parameter from the types ν S̲t̲e̲p̲ i (p , q) and
-- ν′ S̲t̲e̲p̲ i (p , q).

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

S̲t̲e̲p̲ : Container (Proc × Proc) (Proc × Proc)
S̲t̲e̲p̲ =
  (λ { (p , q) → Magic  -- Included in order to aid type inference.
                   ×
                 (∀ {p′ μ} → p [ μ ]⟶ p′ → ∃ λ q′ → q [ μ ]⟶ q′)
                   ×
                 (∀ {q′ μ} → q [ μ ]⟶ q′ → ∃ λ p′ → p [ μ ]⟶ p′)
     })
    ◁
  (λ { {o = p , q} (_ , lr , rl) (p′ , q′) →
       (∃ λ μ → ∃ λ (p⟶p′ : p [ μ ]⟶ p′) → proj₁ (lr p⟶p′) ≡ q′)
         ⊎
       (∃ λ μ → ∃ λ (q⟶q′ : q [ μ ]⟶ q′) → proj₁ (rl q⟶q′) ≡ p′)
       })

-- The definition of Step in terms of a container is pointwise
-- isomorphic to the direct definition.

Step↔S̲t̲e̲p̲ :
  ∀ {r} {R : Rel r Proc} {p q} → Step R p q ↔ ⟦ S̲t̲e̲p̲ ⟧₂ R p q
Step↔S̲t̲e̲p̲ {R = R} {p} {q} = record
  { surjection = record
    { logical-equivalence = record
      { to   = λ s → to₁ s , to₂ s
      ; from = from
      }
    ; right-inverse-of = λ where
        (_ , f) →
          Σ-≡,≡→≡ refl $
            implicit-extensionality ext λ _ → ext (to₂∘from f)
    }
  ; left-inverse-of = λ _ → refl
  }
  where
  to₁ : Step R p q → Container.Shape S̲t̲e̲p̲ (p , q)
  to₁ Step.⟨ lr , rl ⟩ =
      _
    , (λ p⟶p′ → Σ-map id proj₁ (lr p⟶p′))
    , (λ q⟶q′ → Σ-map id proj₁ (rl q⟶q′))

  to₂ :
    (s : Step R p q) →
    Container.Position S̲t̲e̲p̲ (to₁ s) →⋆ uncurry R
  to₂ Step.⟨ lr , _ ⟩ (inj₁ (_ , p⟶p′ , refl)) = proj₂ (proj₂ (lr p⟶p′))
  to₂ Step.⟨ _ , rl ⟩ (inj₂ (_ , q⟶q′ , refl)) = proj₂ (proj₂ (rl q⟶q′))

  from : ⟦ S̲t̲e̲p̲ ⟧₂ R p q → Step R p q
  from ((_ , lr , rl) , f) =
    Step.⟨ (λ p⟶p′ →
              let q′ , q⟶q′ = lr p⟶p′
              in  q′ , q⟶q′ , f (inj₁ (_ , p⟶p′ , refl)))
         , (λ q⟶q′ →
              let p′ , p⟶p′ = rl q⟶q′
              in  p′ , p⟶p′ , f (inj₂ (_ , q⟶q′ , refl)))
         ⟩

  to₂∘from :
    ∀ {p′ q′} {s : Container.Shape S̲t̲e̲p̲ (p , q)}
    (f : Container.Position S̲t̲e̲p̲ s →⋆ uncurry R) →
    (pos : Container.Position S̲t̲e̲p̲ s (p′ , q′)) →
    to₂ (from (s , f)) pos ≡ f pos
  to₂∘from f (inj₁ (_ , _ , refl)) = refl
  to₂∘from f (inj₂ (_ , _ , refl)) = refl

-- The interpretation of S̲t̲e̲p̲ is monotone.

S̲t̲e̲p̲-monotone :
  ∀ {ℓ₁ ℓ₂} → Monotone-∀ ⟦ S̲t̲e̲p̲ ⟧₂ ℓ₁ ℓ₂
S̲t̲e̲p̲-monotone {R = R} {S = S} =
  R ⊆ S                      ↝⟨ Step-monotone ⟩
  Step R ⊆ Step S            ↝⟨ _⇔_.to (∀-cong-⇔ λ _ → ∀-cong-⇔ λ _ → →-cong-⇔
                                  (_↔_.logical-equivalence Step↔S̲t̲e̲p̲)
                                  (_↔_.logical-equivalence Step↔S̲t̲e̲p̲)) ⟩□
  ⟦ S̲t̲e̲p̲ ⟧₂ R ⊆ ⟦ S̲t̲e̲p̲ ⟧₂ S  □

module S̲t̲e̲p̲ {r} {_R_ : Rel r Proc} {p q} where

  -- A "constructor".

  ⟨_,_⟩ :
    (∀ {p′ μ} → p [ μ ]⟶ p′ → ∃ λ q′ → q [ μ ]⟶ q′ × p′ R q′) →
    (∀ {q′ μ} → q [ μ ]⟶ q′ → ∃ λ p′ → p [ μ ]⟶ p′ × p′ R q′) →
    ⟦ S̲t̲e̲p̲ ⟧₂ _R_ p q
  ⟨ lr , rl ⟩ = _↔_.to Step↔S̲t̲e̲p̲ Step.⟨ lr , rl ⟩

  -- Some "projections".

  left-to-right :
    ⟦ S̲t̲e̲p̲ ⟧₂ _R_ p q →
    ∀ {p′ μ} → p [ μ ]⟶ p′ → ∃ λ q′ → q [ μ ]⟶ q′ × p′ R q′
  left-to-right = Step.left-to-right ∘ _↔_.from Step↔S̲t̲e̲p̲

  right-to-left :
    ⟦ S̲t̲e̲p̲ ⟧₂ _R_ p q →
    ∀ {q′ μ} → q [ μ ]⟶ q′ → ∃ λ p′ → p [ μ ]⟶ p′ × p′ R q′
  right-to-left = Step.right-to-left ∘ _↔_.from Step↔S̲t̲e̲p̲

open Temporarily-private public
