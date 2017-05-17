------------------------------------------------------------------------
-- Closure properties for Compatible and Size-preserving
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Up-to.Closure where

open import Equality.Propositional
open import Logical-equivalence using (_⇔_)
open import Prelude

open import Bijection equality-with-J using (_↔_)
open import Function-universe equality-with-J hiding (id; _∘_)

open import Indexed-container
open import Indexed-container.Combinators hiding (id)
open import Relation
open import Up-to

------------------------------------------------------------------------
-- Closure properties for Compatible

-- The results in this section are closely related to
-- Proposition 6.3.21 in Pous and Sangiorgi's "Enhancements of the
-- bisimulation proof method".

-- The function flip Compatible F is closed under _⊗_, assuming that F
-- is monotone.

Compatible-⊗ :
  ∀ {ℓ} {I : Set ℓ} {C₁ C₂ : Container I I} {F : Trans ℓ I} →
  Monotone F →
  Compatible C₁ F → Compatible C₂ F → Compatible (C₁ ⊗ C₂) F
Compatible-⊗ {C₁ = C₁} {C₂} {F} mono comp₁ comp₂ R =
  F (⟦ C₁ ⊗ C₂ ⟧ R)            ⊆⟨ mono (_↔_.to (⟦⊗⟧↔ C₁ C₂)) ⟩
  F (⟦ C₁ ⟧ R ∩ ⟦ C₂ ⟧ R)      ⊆⟨ (λ x → mono proj₁ x , mono proj₂ x) ⟩
  F (⟦ C₁ ⟧ R) ∩ F (⟦ C₂ ⟧ R)  ⊆⟨ Σ-map (comp₁ _) (comp₂ _) ⟩
  ⟦ C₁ ⟧ (F R) ∩ ⟦ C₂ ⟧ (F R)  ⊆⟨ _↔_.from (⟦⊗⟧↔ C₁ C₂) ⟩∎
  ⟦ C₁ ⊗ C₂ ⟧ (F R)            ∎

-- The function flip Compatible F is closed under reindex₁, assuming
-- that F satisfies certain properties.

Compatible-reindex₁ :
  ∀ {ℓ} {I : Set ℓ} {C : Container I I} {F : Trans ℓ I} {f : I → I} →
  Monotone F →
  (∀ {R} → F (R ∘ f) ⊆ F R ∘ f) →
  Compatible C F → Compatible (reindex₁ f C) F
Compatible-reindex₁ {C = C} {F} {f} mono hyp comp R =
  F (⟦ reindex₁ f C ⟧ R)  ⊆⟨ mono (_↔_.to (⟦reindex₁⟧↔ C)) ⟩
  F (⟦ C ⟧ (R ∘ f))       ⊆⟨ comp _ ⟩
  ⟦ C ⟧ (F (R ∘ f))       ⊆⟨ map C hyp ⟩
  ⟦ C ⟧ (F R ∘ f)         ⊆⟨ _↔_.from (⟦reindex₁⟧↔ C) ⟩∎
  ⟦ reindex₁ f C ⟧ (F R)  ∎

-- The function flip Compatible F is closed under reindex₂, assuming
-- that F satisfies a certain property.

Compatible-reindex₂ :
  ∀ {ℓ} {I : Set ℓ} {C : Container I I} {F : Trans ℓ I} {f : I → I} →
  (∀ {R} → F (R ∘ f) ⊆ F R ∘ f) →
  Compatible C F → Compatible (reindex₂ f C) F
Compatible-reindex₂ {C = C} {F} {f} hyp comp R =
  F (⟦ reindex₂ f C ⟧ R)  ⊆⟨⟩
  F (⟦ C ⟧ R ∘ f)         ⊆⟨ hyp ⟩
  F (⟦ C ⟧ R) ∘ f         ⊆⟨ comp _ ⟩
  ⟦ C ⟧ (F R) ∘ f         ⊆⟨ id ⟩∎
  ⟦ reindex₂ f C ⟧ (F R)  ∎

-- The function flip Compatible F is closed under reindex, assuming
-- that F satisfies certain properties.

Compatible-reindex :
  ∀ {ℓ} {I : Set ℓ} {C : Container I I} {F : Trans ℓ I} {f : I → I} →
  Monotone F →
  (∀ {R} → F (R ∘ f) ⊆ F R ∘ f) →
  Compatible C F → Compatible (reindex f C) F
Compatible-reindex {C = C} {F} {f} mono hyp =
  Compatible C F                            ↝⟨ Compatible-reindex₁ mono hyp ⟩
  Compatible (reindex₁ f C) F               ↝⟨ Compatible-reindex₂ hyp ⟩
  Compatible (reindex₂ f (reindex₁ f C)) F  ↔⟨⟩
  Compatible (reindex f C) F                □

-- The function flip Compatible F is closed under _⟷_, assuming that F
-- satisfies certain properties.

Compatible-⟷ :
  ∀ {ℓ} {I : Set ℓ}
    {C₁ C₂ : Container (I × I) (I × I)} {F : Trans₂ ℓ I} →
  Monotone F →
  (∀ {R} → F (R ∘ swap) ⊆ F R ∘ swap) →
  Compatible C₁ F → Compatible C₂ F → Compatible (C₁ ⟷ C₂) F
Compatible-⟷ {C₁ = C₁} {C₂} {F} mono sym = curry (
  Compatible C₁ F × Compatible C₂ F                 ↝⟨ Σ-map id (Compatible-reindex mono sym) ⟩
  Compatible C₁ F × Compatible (reindex swap C₂) F  ↝⟨ uncurry (Compatible-⊗ mono) ⟩
  Compatible (C₁ ⊗ reindex swap C₂) F               ↔⟨⟩
  Compatible (C₁ ⟷ C₂) F                            □)

------------------------------------------------------------------------
-- Closure properties for Size-preserving

-- The function flip Size-preserving F is closed under reindex,
-- assuming that F satisfies certain properties.
--
-- Note that the assumptions are different from the ones asked for in
-- Compatible-reindex: monotonicity of F has been replaced by the
-- assumption that f is an involution.

Size-preserving-reindex :
  ∀ {ℓ} {I : Set ℓ} {C : Container I I} {F : Trans ℓ I} {f : I → I} →
  f ∘ f ≡ id →
  (∀ {R} → F (R ∘ f) ⊆ F R ∘ f) →
  Size-preserving C F → Size-preserving (reindex f C) F
Size-preserving-reindex {C = C} {F} {f}
                        idem hyp pres {R = R} {i = i} R⊆ =

  F R                        ⊆⟨ (λ {x} → subst (λ g → F (R ∘ g) x) (sym idem)) ⟩
  F (R ∘ f ∘ f)              ⊆⟨ hyp ⟩
  F (R ∘ f) ∘ f              ⊆⟨ pres (

      R ∘ f                       ⊆⟨ R⊆ ⟩
      ν (reindex f C) i ∘ f       ⊆⟨ _⇔_.to (ν-reindex⇔ idem) ⟩
      ν C i ∘ f ∘ f               ⊆⟨ (λ {x} → subst (λ g → ν C i (g x)) idem) ⟩∎
      ν C i                       ∎) ⟩

  ν C i ∘ f                  ⊆⟨ _⇔_.from (ν-reindex⇔ idem) ⟩∎
  ν (reindex f C) i          ∎

-- TODO: Can one prove or disprove that Size-preserving is closed
-- under _⊗_ and/or _⟷_?
