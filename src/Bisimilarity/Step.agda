------------------------------------------------------------------------
-- The Step function, used to define strong and weak bisimilarity as
-- well as expansion
------------------------------------------------------------------------

{-# OPTIONS --sized-types #-}

open import Prelude

open import Labelled-transition-system

module Bisimilarity.Step
         {ℓ}
         (lts : LTS ℓ)
         (open LTS lts)
         (_[_]↝₁_ _[_]↝₂_ : Proc → Label → Proc → Type ℓ)
         where

open import Equality.Propositional
open import Logical-equivalence using (_⇔_)

open import Bijection equality-with-J using (_↔_)
import Equivalence equality-with-J as Eq
open import Function-universe equality-with-J as F hiding (_∘_)
open import H-level.Closure equality-with-J

import Similarity.Step lts as One-sided
open import Indexed-container hiding (⟨_⟩)
open import Indexed-container.Combinators hiding (_∘_)
open import Relation

private
 module Temporarily-private where

  -- If _[_]↝₁_ and _[_]↝₂_ are instantiated with _[_]⟶_, then this is
  -- basically the function from Definition 6.3.1 in Pous and
  -- Sangiorgi's "Enhancements of the bisimulation proof method",
  -- except that clause (3) is omitted.
  --
  -- Similarly, if the relations are instantiated with _[_]⇒̂_, then
  -- this is basically the function wb₁, again with the exception that
  -- clause (3) is omitted.
  --
  -- Finally, if _[_]↝₁_ is instantiated with _[_]⟶̂_ and _[_]↝₂_ is
  -- instantiated with _[_]⇒_, then we get the expansion relation's
  -- "step" function.

  record Step {r} (R : Rel₂ r Proc) (pq : Proc × Proc) :
              Type (ℓ ⊔ r) where
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

-- The Step function, expressed as an indexed container.

StepC : Container (Proc × Proc) (Proc × Proc)
StepC = One-sided.StepC _[_]↝₁_ ⟷ One-sided.StepC _[_]↝₂_

-- The strong bisimilarity container presented in the paper,
-- generalised to use _[_]↝₁_ and _[_]↝₂_.

StepC′ : Container (Proc × Proc) (Proc × Proc)
StepC′ =
  (λ { (p , q) → (∀ {p′ μ} → p [ μ ]⟶ p′ → ∃ λ q′ → q [ μ ]↝₁ q′) ×
                 (∀ {q′ μ} → q [ μ ]⟶ q′ → ∃ λ p′ → p [ μ ]↝₂ p′)
     })
    ◁
  (λ { {(p , q)} (lr , rl) (p′ , q′) →
       (∃ λ μ → ∃ λ (p⟶p′ : p [ μ ]⟶ p′) → proj₁ (lr p⟶p′) ≡ q′) ⊎
       (∃ λ μ → ∃ λ (q⟶q′ : q [ μ ]⟶ q′) → proj₁ (rl q⟶q′) ≡ p′)
     })

-- The interpretations of the two containers above are pointwise
-- logically equivalent, and in the presence of extensionality they
-- are pointwise isomorphic.

StepC↔StepC′ :
  ∀ {k r} {R : Rel₂ r Proc} {pq} →
  Extensionality? k ℓ (ℓ ⊔ r) →
  ⟦ StepC ⟧ R pq ↝[ k ] ⟦ StepC′ ⟧ R pq
StepC↔StepC′ {pq = p , q} =
  inverse-ext? λ {k} ext →
  Σ-cong (inverse $
          drop-⊤-left-Σ (One-sided.Magic↔⊤ _)
            ×-cong
          drop-⊤-left-Σ (One-sided.Magic↔⊤ _)) λ { (lr , rl) →
  implicit-∀-cong ext λ { {p′ , q′} →
  Π-cong (lower-extensionality? k lzero ℓ ext)
    (F.id ⊎-cong (

       (∃ λ μ → ∃ λ (q⟶q′ : q [ μ ]⟶ q′) →
            proj₁ (rl q⟶q′) ≡ p′)                            ↝⟨ inverse $ drop-⊤-left-Σ (_⇔_.to contractible⇔↔⊤ (singleton-contractible _)) ⟩

       (∃ λ (q′p′≡ : ∃ λ q′p′ → q′p′ ≡ (q′ , p′)) →
        ∃ λ μ → ∃ λ (q⟶q′ : q [ μ ]⟶ proj₁ (proj₁ q′p′≡)) →
          proj₁ (rl q⟶q′) ≡ proj₂ (proj₁ q′p′≡))             ↝⟨ inverse Σ-assoc ⟩

       (∃ λ q′p′ → q′p′ ≡ (q′ , p′) ×
        ∃ λ μ → ∃ λ (q⟶q′ : q [ μ ]⟶ proj₁ q′p′) →
          proj₁ (rl q⟶q′) ≡ proj₂ q′p′)                      ↔⟨ (∃-cong λ _ → (inverse $ Eq.≃-≡ (Eq.↔⇒≃ ×-comm)) ×-cong F.id) ⟩□

       (∃ λ q′p′ → swap q′p′ ≡ (p′ , q′) ×
        ∃ λ μ → ∃ λ (q⟶q′ : q [ μ ]⟶ proj₁ q′p′) →
          proj₁ (rl q⟶q′) ≡ proj₂ q′p′)                      □))

    (λ _ → F.id) }}

-- The definition of Step in terms of a container is pointwise
-- logically equivalent to the direct definition, and in the presence
-- of extensionality it is pointwise isomorphic to the direct
-- definition.

Step↔StepC :
  ∀ {k r} {R : Rel₂ r Proc} {pq} →
  Extensionality? k ℓ (ℓ ⊔ r) →
  Step R pq ↝[ k ] ⟦ StepC ⟧ R pq
Step↔StepC {R = R} {pq} ext =
  Step R pq                                     ↔⟨ lemma ⟩

  One-sided.Step _[_]↝₁_ R pq
    ×
  One-sided.Step _[_]↝₂_ (R ⁻¹) (swap pq)       ↝⟨ One-sided.Step↔StepC _ ext ×-cong One-sided.Step↔StepC _ ext ⟩

  ⟦ One-sided.StepC _[_]↝₁_ ⟧ R pq
    ×
  ⟦ One-sided.StepC _[_]↝₂_ ⟧ (R ⁻¹) (swap pq)  ↝⟨ inverse-ext? (λ ext → ⟦⟷⟧↔ ext (One-sided.StepC _[_]↝₁_) (One-sided.StepC _[_]↝₂_)) ext ⟩□

  ⟦ StepC ⟧ R pq                                □
  where
  lemma : _ ↔ _
  lemma = record
    { surjection = record
      { logical-equivalence = record
        { to   = λ s → One-sided.⟨ Step.left-to-right s ⟩
                     , One-sided.⟨ Step.right-to-left s ⟩
        ; from = λ { (lr , rl) →
                     Temporarily-private.⟨ One-sided.Step.challenge lr
                                         , One-sided.Step.challenge rl
                                         ⟩
                   }
        }
      ; right-inverse-of = λ _ → refl
      }
    ; left-inverse-of = λ _ → refl
    }

-- A variant of the previous lemma, stated for StepC′ instead of
-- StepC.

Step↔StepC′ :
  ∀ {k r} {R : Rel₂ r Proc} {pq} →
  Extensionality? k ℓ (ℓ ⊔ r) →
  Step R pq ↝[ k ] ⟦ StepC′ ⟧ R pq
Step↔StepC′ {R = R} {pq} ext =
  Step R pq        ↝⟨ Step↔StepC   ext ⟩
  ⟦ StepC  ⟧ R pq  ↝⟨ StepC↔StepC′ ext ⟩□
  ⟦ StepC′ ⟧ R pq  □

module StepC {r} {R : Rel₂ r Proc} {p q} where

  -- A "constructor".

  ⟨_,_⟩ :
    (∀ {p′ μ} → p [ μ ]⟶ p′ → ∃ λ q′ → q [ μ ]↝₁ q′ × R (p′ , q′)) →
    (∀ {q′ μ} → q [ μ ]⟶ q′ → ∃ λ p′ → p [ μ ]↝₂ p′ × R (p′ , q′)) →
    ⟦ StepC ⟧ R (p , q)
  ⟨ lr , rl ⟩ = _⇔_.to (Step↔StepC _) Temporarily-private.⟨ lr , rl ⟩

  -- Some "projections".

  left-to-right :
    ⟦ StepC ⟧ R (p , q) →
    ∀ {p′ μ} → p [ μ ]⟶ p′ → ∃ λ q′ → q [ μ ]↝₁ q′ × R (p′ , q′)
  left-to-right = Step.left-to-right ∘ _⇔_.from (Step↔StepC _)

  right-to-left :
    ⟦ StepC ⟧ R (p , q) →
    ∀ {q′ μ} → q [ μ ]⟶ q′ → ∃ λ p′ → p [ μ ]↝₂ p′ × R (p′ , q′)
  right-to-left = Step.right-to-left ∘ _⇔_.from (Step↔StepC _)

open Temporarily-private public
