------------------------------------------------------------------------
-- The Step function, used to define strong and weak bisimilarity as
-- well as expansion
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

open import Labelled-transition-system

module Bisimilarity.Step
         (lts : LTS)
         (open LTS lts)
         (_[_]↝₁_ _[_]↝₂_ : Proc → Label → Proc → Set)
         where

open import Equality.Propositional
open import Interval using (ext)
open import Logical-equivalence using (_⇔_)
open import Prelude

open import Bijection equality-with-J using (_↔_)
open import Function-universe equality-with-J hiding (id; _∘_)

open import Indexed-container hiding (⟨_⟩)
open import Relation

private
 module Temporarily-private where

  -- If _[_]↝₁_ and _[_]↝₂_ are instantiated with _[_]⟶_, then this is
  -- basically the function from Definition 6.3.1 in Pous and
  -- Sangiorgi's "Enhancements of the bisimulation proof method",
  -- except that clause (3) is omitted. Similarly, if the relations
  -- are instantiated with _[_]⇒̂_, then this is basically the function
  -- wb₁, again with the exception that clause (3) is omitted.
  -- Finally, if _[_]↝₁_ is instantiated with _[_]⟶̂_ and _[_]↝₂_ is
  -- instantiated with _[_]⇒̂_, then we get the expansion relation's
  -- "step" function.

  record Step {r} (R : Rel₂ r Proc) (pq : Proc × Proc) : Set r where
    constructor ⟨_,_⟩

    private
      p = proj₁ pq
      q = proj₂ pq

    field
      left-to-right : ∀ {p′ μ} →
                      p [ μ ]⟶ p′ → ∃ λ q′ → q [ μ ]↝₁ q′ × R (p′ , q′)
      right-to-left : ∀ {q′ μ} →
                      q [ μ ]⟶ q′ → ∃ λ p′ → p [ μ ]↝₂ p′ × R (p′ , q′)

open Temporarily-private using (Step)

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
                 (∀ {p′ μ} → p [ μ ]⟶ p′ → ∃ λ q′ → q [ μ ]↝₁ q′)
                   ×
                 (∀ {q′ μ} → q [ μ ]⟶ q′ → ∃ λ p′ → p [ μ ]↝₂ p′)
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
  ∀ {r} {R : Rel₂ r Proc} {pq} → Step R pq ↔ ⟦ S̲t̲e̲p̲ ⟧ R pq
Step↔S̲t̲e̲p̲ {R = R} {pq} = record
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
  to₁ : Step R pq → Container.Shape S̲t̲e̲p̲ pq
  to₁ Step.⟨ lr , rl ⟩ =
      _
    , (λ p⟶p′ → Σ-map id proj₁ (lr p⟶p′))
    , (λ q⟶q′ → Σ-map id proj₁ (rl q⟶q′))

  to₂ :
    (s : Step R pq) →
    Container.Position S̲t̲e̲p̲ (to₁ s) ⊆ R
  to₂ Step.⟨ lr , _ ⟩ (inj₁ (_ , p⟶p′ , refl)) = proj₂ (proj₂ (lr p⟶p′))
  to₂ Step.⟨ _ , rl ⟩ (inj₂ (_ , q⟶q′ , refl)) = proj₂ (proj₂ (rl q⟶q′))

  from : ⟦ S̲t̲e̲p̲ ⟧ R pq → Step R pq
  from ((_ , lr , rl) , f) =
    Step.⟨ (λ p⟶p′ →
              let q′ , q⟶q′ = lr p⟶p′
              in  q′ , q⟶q′ , f (inj₁ (_ , p⟶p′ , refl)))
         , (λ q⟶q′ →
              let p′ , p⟶p′ = rl q⟶q′
              in  p′ , p⟶p′ , f (inj₂ (_ , q⟶q′ , refl)))
         ⟩

  to₂∘from :
    ∀ {p′q′} {s : Container.Shape S̲t̲e̲p̲ pq}
    (f : Container.Position S̲t̲e̲p̲ s ⊆ R) →
    (pos : Container.Position S̲t̲e̲p̲ s p′q′) →
    to₂ (from (s , f)) pos ≡ f pos
  to₂∘from f (inj₁ (_ , _ , refl)) = refl
  to₂∘from f (inj₂ (_ , _ , refl)) = refl

module S̲t̲e̲p̲ {r} {R : Rel₂ r Proc} {p q} where

  -- A "constructor".

  ⟨_,_⟩ :
    (∀ {p′ μ} → p [ μ ]⟶ p′ → ∃ λ q′ → q [ μ ]↝₁ q′ × R (p′ , q′)) →
    (∀ {q′ μ} → q [ μ ]⟶ q′ → ∃ λ p′ → p [ μ ]↝₂ p′ × R (p′ , q′)) →
    ⟦ S̲t̲e̲p̲ ⟧ R (p , q)
  ⟨ lr , rl ⟩ = _↔_.to Step↔S̲t̲e̲p̲ Step.⟨ lr , rl ⟩

  -- Some "projections".

  left-to-right :
    ⟦ S̲t̲e̲p̲ ⟧ R (p , q) →
    ∀ {p′ μ} → p [ μ ]⟶ p′ → ∃ λ q′ → q [ μ ]↝₁ q′ × R (p′ , q′)
  left-to-right = Step.left-to-right ∘ _↔_.from Step↔S̲t̲e̲p̲

  right-to-left :
    ⟦ S̲t̲e̲p̲ ⟧ R (p , q) →
    ∀ {q′ μ} → q [ μ ]⟶ q′ → ∃ λ p′ → p [ μ ]↝₂ p′ × R (p′ , q′)
  right-to-left = Step.right-to-left ∘ _↔_.from Step↔S̲t̲e̲p̲

open Temporarily-private public
