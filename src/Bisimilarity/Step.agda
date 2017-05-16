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
open import Prelude

open import Bijection equality-with-J using (_↔_)
open import Function-universe equality-with-J hiding (_∘_)

import Similarity.Step lts as One-sided
open import Indexed-container hiding (⟨_⟩)
open import Indexed-container.Combinators
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

-- The Step function, expressed as an indexed container.

S̲t̲e̲p̲ : Container (Proc × Proc) (Proc × Proc)
S̲t̲e̲p̲ =
  One-sided.S̲t̲e̲p̲ _[_]↝₁_
    ⊗
  reindex₂ swap (reindex₁ swap (One-sided.S̲t̲e̲p̲ _[_]↝₂_))

-- The definition of Step in terms of a container is pointwise
-- isomorphic to the direct definition.

Step↔S̲t̲e̲p̲ :
  ∀ {r} {R : Rel₂ r Proc} {pq} → Step R pq ↔ ⟦ S̲t̲e̲p̲ ⟧ R pq
Step↔S̲t̲e̲p̲ {R = R} {pq} =
  Step R pq                                                        ↝⟨ lemma ⟩

  One-sided.Step _[_]↝₁_ R pq
    ×
  One-sided.Step _[_]↝₂_ (R ∘ swap) (swap pq)                      ↝⟨ One-sided.Step↔S̲t̲e̲p̲ _ ×-cong One-sided.Step↔S̲t̲e̲p̲ _ ⟩

  ⟦ One-sided.S̲t̲e̲p̲ _[_]↝₁_ ⟧ R pq
    ×
  ⟦ One-sided.S̲t̲e̲p̲ _[_]↝₂_ ⟧ (R ∘ swap) (swap pq)                  ↔⟨⟩

  ⟦ One-sided.S̲t̲e̲p̲ _[_]↝₁_ ⟧ R pq
    ×
  ⟦ reindex₂ swap (One-sided.S̲t̲e̲p̲ _[_]↝₂_) ⟧ (R ∘ swap) pq         ↝⟨ (∃-cong λ _ → inverse $
                                                                       ⟦reindex₁⟧ (reindex₂ swap (One-sided.S̲t̲e̲p̲ _[_]↝₂_))) ⟩
  ⟦ One-sided.S̲t̲e̲p̲ _[_]↝₁_ ⟧ R pq
    ×
  ⟦ reindex₁ swap (reindex₂ swap (One-sided.S̲t̲e̲p̲ _[_]↝₂_)) ⟧ R pq  ↝⟨ inverse $
                                                                      ⟦⊗⟧ (One-sided.S̲t̲e̲p̲ _[_]↝₁_)
                                                                          (reindex₁ swap (reindex₂ swap (One-sided.S̲t̲e̲p̲ _[_]↝₂_))) ⟩□
  ⟦ S̲t̲e̲p̲ ⟧ R pq                                                    □
  where
  lemma = record
    { surjection = record
      { logical-equivalence = record
        { to   = λ s → One-sided.Step.⟨ Step.left-to-right s ⟩
                     , One-sided.Step.⟨ Step.right-to-left s ⟩
        ; from = λ { (lr , rl) → Step.⟨ One-sided.Step.challenge lr
                                      , One-sided.Step.challenge rl
                                      ⟩
                   }
        }
      ; right-inverse-of = λ _ → refl
      }
    ; left-inverse-of = λ _ → refl
    }

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
