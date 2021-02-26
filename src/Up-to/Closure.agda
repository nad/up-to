------------------------------------------------------------------------
-- Closure properties for Compatible and Size-preserving
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe --sized-types #-}

module Up-to.Closure where

open import Equality.Propositional
open import Logical-equivalence using (_⇔_)
open import Prelude as P
open import Prelude.Size

open import Bijection equality-with-J using (_↔_)
open import Function-universe equality-with-J hiding (id; _∘_)

import Bisimilarity
open import Indexed-container hiding (Bisimilarity)
open import Indexed-container.Combinators hiding (id; _∘_)
open import Labelled-transition-system
import Labelled-transition-system.CCS
open import Relation
import Similarity
import Similarity.CCS as SC
open import Up-to

private
  module CCS {ℓ} (Name : Type ℓ) where
    open Labelled-transition-system.CCS Name public
    open module B = Bisimilarity CCS public
    open module S = Similarity CCS public using (Similarity)

------------------------------------------------------------------------
-- Closure properties for Compatible

-- The results in this section are closely related to
-- Proposition 6.3.21 in Pous and Sangiorgi's "Enhancements of the
-- bisimulation proof method".

-- The function flip Compatible F is closed under _⊗_, assuming that F
-- is monotone.

Compatible-⊗ :
  ∀ {ℓ} {I : Type ℓ} {C₁ C₂ : Container I I} {F : Trans ℓ I} →
  Monotone F →
  Compatible C₁ F → Compatible C₂ F → Compatible (C₁ ⊗ C₂) F
Compatible-⊗ {C₁ = C₁} {C₂} {F} mono comp₁ comp₂ {R = R} =
  F (⟦ C₁ ⊗ C₂ ⟧ R)            ⊆⟨ mono (⟦⊗⟧↔ _ C₁ C₂) ⟩
  F (⟦ C₁ ⟧ R ∩ ⟦ C₂ ⟧ R)      ⊆⟨ (λ x → mono proj₁ x , mono proj₂ x) ⟩
  F (⟦ C₁ ⟧ R) ∩ F (⟦ C₂ ⟧ R)  ⊆⟨ Σ-map comp₁ comp₂ ⟩
  ⟦ C₁ ⟧ (F R) ∩ ⟦ C₂ ⟧ (F R)  ⊆⟨ _⇔_.from (⟦⊗⟧↔ _ C₁ C₂) ⟩∎
  ⟦ C₁ ⊗ C₂ ⟧ (F R)            ∎

-- The function flip Compatible F is closed under reindex₁ f, assuming
-- that F is monotone and f-symmetric.

Compatible-reindex₁ :
  ∀ {ℓ} {I : Type ℓ} {C : Container I I} {F : Trans ℓ I} {f : I → I} →
  Monotone F → Symmetric f F →
  Compatible C F → Compatible (reindex₁ f C) F
Compatible-reindex₁ {C = C} {F} {f} mono hyp comp {R = R} =
  F (⟦ reindex₁ f C ⟧ R)  ⊆⟨ mono (⟦reindex₁⟧↔ _ C) ⟩
  F (⟦ C ⟧ (R ∘ f))       ⊆⟨ comp ⟩
  ⟦ C ⟧ (F (R ∘ f))       ⊆⟨ map C (hyp _) ⟩
  ⟦ C ⟧ (F R ∘ f)         ⊆⟨ _⇔_.from (⟦reindex₁⟧↔ _ C) ⟩∎
  ⟦ reindex₁ f C ⟧ (F R)  ∎

-- The function flip Compatible F is closed under reindex₂ f, assuming
-- that F is f-symmetric.

Compatible-reindex₂ :
  ∀ {ℓ} {I : Type ℓ} {C : Container I I} {F : Trans ℓ I} {f : I → I} →
  Symmetric f F →
  Compatible C F → Compatible (reindex₂ f C) F
Compatible-reindex₂ {C = C} {F} {f} hyp comp {R = R} =
  F (⟦ reindex₂ f C ⟧ R)  ⊆⟨⟩
  F (⟦ C ⟧ R ∘ f)         ⊆⟨ hyp _ ⟩
  F (⟦ C ⟧ R) ∘ f         ⊆⟨ comp ⟩
  ⟦ C ⟧ (F R) ∘ f         ⊆⟨ id ⟩∎
  ⟦ reindex₂ f C ⟧ (F R)  ∎

-- The function flip Compatible F is closed under reindex f, assuming
-- that F is monotone and f-symmetric.

Compatible-reindex :
  ∀ {ℓ} {I : Type ℓ} {C : Container I I} {F : Trans ℓ I} {f : I → I} →
  Monotone F → Symmetric f F →
  Compatible C F → Compatible (reindex f C) F
Compatible-reindex {C = C} {F} {f} mono hyp =
  Compatible C F                            ↝⟨ Compatible-reindex₁ mono hyp ⟩
  Compatible (reindex₁ f C) F               ↝⟨ Compatible-reindex₂ hyp ⟩
  Compatible (reindex₂ f (reindex₁ f C)) F  ↔⟨⟩
  Compatible (reindex f C) F                □

-- The function flip Compatible F is closed under _⟷_, assuming that F
-- is monotone and symmetric.

Compatible-⟷ :
  ∀ {ℓ} {I : Type ℓ}
    {C₁ C₂ : Container (I × I) (I × I)} {F : Trans₂ ℓ I} →
  Monotone F → Symmetric swap F →
  Compatible C₁ F → Compatible C₂ F → Compatible (C₁ ⟷ C₂) F
Compatible-⟷ {C₁ = C₁} {C₂} {F} mono sym = curry (
  Compatible C₁ F × Compatible C₂ F                 ↝⟨ Σ-map id (Compatible-reindex mono sym) ⟩
  Compatible C₁ F × Compatible (reindex swap C₂) F  ↝⟨ uncurry (Compatible-⊗ mono) ⟩
  Compatible (C₁ ⊗ reindex swap C₂) F               ↔⟨⟩
  Compatible (C₁ ⟷ C₂) F                            □)

-- An instance of the result above: If F is monotone and symmetric,
-- and compatible for strong similarity for some LTS, then F is
-- compatible for strong bisimilarity for this LTS.

compatible-for-similarity→compatible-for-bisimilarity :
  ∀ {ℓ} {lts : LTS ℓ} {F} →
  Monotone F → Symmetric swap F →
  Compatible (Similarity.StepC lts) F →
  Compatible (Bisimilarity.StepC lts) F
compatible-for-similarity→compatible-for-bisimilarity mono sym comp =
  Compatible-⟷ mono sym comp comp

------------------------------------------------------------------------
-- Closure properties for Size-preserving

-- The function flip Size-preserving F is closed under reindex,
-- assuming that F is f-symmetric for an involutory function f.
--
-- Note that the assumptions are different from the ones asked for in
-- Compatible-reindex: monotonicity of F has been replaced by the
-- assumption that f is an involution.

Size-preserving-reindex :
  ∀ {ℓ} {I : Type ℓ} {C : Container I I} {F : Trans ℓ I} {f : I → I} →
  f ∘ f ≡ id → Symmetric f F →
  Size-preserving C F → Size-preserving (reindex f C) F
Size-preserving-reindex {C = C} {F} {f}
                        inv hyp pres {R = R} {i = i} R⊆ =

  F R                        ⊆⟨ (λ {x} → subst (λ g → F (R ∘ g) x) (sym inv)) ⟩
  F (R ∘ f ∘ f)              ⊆⟨ hyp _ ⟩
  F (R ∘ f) ∘ f              ⊆⟨ pres (

      R ∘ f                       ⊆⟨ R⊆ ⟩
      ν (reindex f C) i ∘ f       ⊆⟨ _⇔_.to (ν-reindex⇔ inv) ⟩
      ν C i ∘ f ∘ f               ⊆⟨ (λ {x} → subst (λ g → ν C i (g x)) inv) ⟩∎
      ν C i                       ∎) ⟩

  ν C i ∘ f                  ⊆⟨ _⇔_.from (ν-reindex⇔ inv) ⟩∎
  ν (reindex f C) i          ∎

-- Some negative results:
--
-- * For inhabited name types it is not in general the case that a
--   monotone and symmetric function F that is size-preserving for
--   similarity for CCS is also size-preserving for bisimilarity for
--   CCS.
--
-- * It is not in general the case that if F is monotone and
--   symmetric, and size-preserving for strong similarity for some
--   LTS, then F is size-preserving for strong bisimilarity for this
--   LTS.
--
-- * The function flip Size-preserving F is not closed under _⟷_ for
--   all F, not even those that are monotone and symmetric.
--
-- * Furthermore flip Size-preserving F is not closed under _⊗_ for
--   all F, not even those that are monotone.

¬-Size-preserving-⟷/⊗ :
  ∀ {ℓ} →
  ({Name : Type ℓ} →
   let open CCS Name in
   Name →
   ¬ ({F : Trans₂ ℓ (Proc ∞)} →
      Monotone F → Symmetric swap F →
      Size-preserving S.StepC F →
      Size-preserving B.StepC F))
    ×
  ¬ (∀ {lts : LTS ℓ} {F} →
     Monotone F → Symmetric swap F →
     Size-preserving (Similarity.StepC lts) F →
     Size-preserving (Bisimilarity.StepC lts) F)
    ×
  ¬ ({I : Type ℓ} {C₁ C₂ : Container (I × I) (I × I)}
     {F : Trans₂ ℓ I} →
     Monotone F → Symmetric swap F →
     Size-preserving C₁ F → Size-preserving C₂ F →
     Size-preserving (C₁ ⟷ C₂) F)
    ×
  ¬ ({I : Type ℓ} {C₁ C₂ : Container I I} {F : Trans ℓ I} →
     Monotone F →
     Size-preserving C₁ F → Size-preserving C₂ F →
     Size-preserving (C₁ ⊗ C₂) F)
¬-Size-preserving-⟷/⊗ {ℓ} =
    Lemmas.contradiction₂
  , Lemmas.contradiction₃ (lift tt)
  , Lemmas.contradiction₄ (lift tt)
  , Lemmas.contradiction₅ (lift tt)
  where
  module Lemmas {Name : Type ℓ} (a : Name) where
    open CCS Name public

    ≤≥≁ = SC.≤≥≁ a

    m₁ = proj₁ ≤≥≁
    m₂ = proj₁ (proj₂ ≤≥≁)

    F : Trans₂ ℓ (Proc ∞)
    F R = R ∪ (_≡ (m₁ , m₂)) ∪ (_≡ (m₂ , m₁))

    mono : Monotone F
    mono R⊆S = ⊎-map R⊆S id

    symm : Symmetric swap F
    symm R =
      F (R ⁻¹)                                      ⊆⟨⟩
      R ⁻¹ ∪ (_≡ (m₁ , m₂))    ∪ (_≡ (m₂ , m₁))     ⊆⟨ ⊎-map id P.[ inj₂ ∘ lemma , inj₁ ∘ lemma ] ⟩
      R ⁻¹ ∪ (_≡ (m₁ , m₂)) ⁻¹ ∪ (_≡ (m₂ , m₁)) ⁻¹  ⊆⟨ id ⟩∎
      F R ⁻¹                                        ∎
      where
      lemma : {p₁ p₂ : Proc ∞ × Proc ∞} → p₁ ≡ swap p₂ → swap p₁ ≡ p₂
      lemma refl = refl

    pres : Size-preserving S.StepC F
    pres {R = R} {i = i} R⊆ =
      F R                                  ⊆⟨⟩
      R ∪ (_≡ (m₁ , m₂)) ∪ (_≡ (m₂ , m₁))  ⊆⟨ [ R⊆ , helper ] ⟩∎
      Similarity i                         ∎
      where
      helper : ∀ {p} → p ≡ (m₁ , m₂) ⊎ p ≡ (m₂ , m₁) → Similarity i p
      helper (inj₁ refl) = proj₁ (proj₂ (proj₂ ≤≥≁))
      helper (inj₂ refl) = proj₁ (proj₂ (proj₂ (proj₂ ≤≥≁)))

    contradiction =
      Size-preserving B.StepC F            ↝⟨ (λ hyp → _⇔_.to (monotone→⇔ _ mono) hyp) ⟩
      F (Bisimilarity ∞) ⊆ Bisimilarity ∞  ↝⟨ _$ inj₂ (inj₁ refl) ⟩
      m₁ ∼ m₂                              ↝⟨ proj₂ (proj₂ (proj₂ (proj₂ ≤≥≁))) ⟩□
      ⊥                                    □

    contradiction₂ =
      ({F : Trans₂ ℓ (Proc ∞)} →
       Monotone F → Symmetric swap F →
       Size-preserving S.StepC F →
       Size-preserving B.StepC F)       ↝⟨ (λ closed → closed mono symm pres) ⟩

      Size-preserving B.StepC F         ↝⟨ contradiction ⟩□

      ⊥                                 □

    contradiction₃ =
      (∀ {lts : LTS ℓ} {F} →
       Monotone F → Symmetric swap F →
       Size-preserving (Similarity.StepC lts) F →
       Size-preserving (Bisimilarity.StepC lts) F)        ↝⟨ (λ closed mono sym pres → closed mono sym pres) ⟩

      ({F : Trans₂ ℓ (Proc ∞)} →
       Monotone F → Symmetric swap F →
       Size-preserving S.StepC F →
       Size-preserving B.StepC F)                         ↝⟨ contradiction₂ ⟩□

      ⊥                                                   □

    contradiction₄ =
      ({I : Type ℓ} {C₁ C₂ : Container (I × I) (I × I)}
       {F : Trans₂ ℓ I} →
       Monotone F → Symmetric swap F →
       Size-preserving C₁ F → Size-preserving C₂ F →
       Size-preserving (C₁ ⟷ C₂) F)                       ↝⟨ (λ closed mono symm pres → closed mono symm pres pres) ⟩

      (∀ {lts : LTS ℓ} {F} →
       Monotone F → Symmetric swap F →
       Size-preserving (Similarity.StepC lts) F →
       Size-preserving (Bisimilarity.StepC lts) F)        ↝⟨ contradiction₃ ⟩□

      ⊥                                                   □

    contradiction₅ =
      ({I : Type ℓ} {C₁ C₂ : Container I I}
       {F : Trans ℓ I} →
       Monotone F →
       Size-preserving C₁ F → Size-preserving C₂ F →
       Size-preserving (C₁ ⊗ C₂) F)                   ↝⟨ (λ closed → closed mono pres) ⟩

      (Size-preserving (reindex swap S.StepC) F →
       Size-preserving B.StepC F)                     ↝⟨ _$ Size-preserving-reindex refl symm pres ⟩

      Size-preserving B.StepC F                       ↝⟨ contradiction ⟩□

      ⊥                                               □
