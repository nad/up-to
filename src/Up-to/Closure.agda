------------------------------------------------------------------------
-- Closure properties for Compatible and Size-preserving
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Up-to.Closure where

open import Equality.Propositional
open import Logical-equivalence using (_⇔_)
open import Prelude as P

open import Bijection equality-with-J using (_↔_)
open import Function-universe equality-with-J hiding (id; _∘_)

open import Indexed-container hiding (Bisimilarity)
open import Indexed-container.Combinators hiding (id; _∘_)
open import Labelled-transition-system.CCS ⊤ hiding (ν)
open import Relation
import Similarity.Strong.CCS as SC
open import Up-to

open import Bisimilarity.Coinductive CCS as B
open import Similarity.Strong CCS as S

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

-- The function flip Compatible F is closed under reindex₁ f, assuming
-- that F is monotone and f-symmetric.

Compatible-reindex₁ :
  ∀ {ℓ} {I : Set ℓ} {C : Container I I} {F : Trans ℓ I} {f : I → I} →
  Monotone F → Symmetric f F →
  Compatible C F → Compatible (reindex₁ f C) F
Compatible-reindex₁ {C = C} {F} {f} mono hyp comp R =
  F (⟦ reindex₁ f C ⟧ R)  ⊆⟨ mono (_↔_.to (⟦reindex₁⟧↔ C)) ⟩
  F (⟦ C ⟧ (R ∘ f))       ⊆⟨ comp _ ⟩
  ⟦ C ⟧ (F (R ∘ f))       ⊆⟨ map C (hyp _) ⟩
  ⟦ C ⟧ (F R ∘ f)         ⊆⟨ _↔_.from (⟦reindex₁⟧↔ C) ⟩∎
  ⟦ reindex₁ f C ⟧ (F R)  ∎

-- The function flip Compatible F is closed under reindex₂ f, assuming
-- that F is f-symmetric.

Compatible-reindex₂ :
  ∀ {ℓ} {I : Set ℓ} {C : Container I I} {F : Trans ℓ I} {f : I → I} →
  Symmetric f F →
  Compatible C F → Compatible (reindex₂ f C) F
Compatible-reindex₂ {C = C} {F} {f} hyp comp R =
  F (⟦ reindex₂ f C ⟧ R)  ⊆⟨⟩
  F (⟦ C ⟧ R ∘ f)         ⊆⟨ hyp _ ⟩
  F (⟦ C ⟧ R) ∘ f         ⊆⟨ comp _ ⟩
  ⟦ C ⟧ (F R) ∘ f         ⊆⟨ id ⟩∎
  ⟦ reindex₂ f C ⟧ (F R)  ∎

-- The function flip Compatible F is closed under reindex f, assuming
-- that F is monotone and f-symmetric.

Compatible-reindex :
  ∀ {ℓ} {I : Set ℓ} {C : Container I I} {F : Trans ℓ I} {f : I → I} →
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
  ∀ {ℓ} {I : Set ℓ}
    {C₁ C₂ : Container (I × I) (I × I)} {F : Trans₂ ℓ I} →
  Monotone F → Symmetric swap F →
  Compatible C₁ F → Compatible C₂ F → Compatible (C₁ ⟷ C₂) F
Compatible-⟷ {C₁ = C₁} {C₂} {F} mono sym = curry (
  Compatible C₁ F × Compatible C₂ F                 ↝⟨ Σ-map id (Compatible-reindex mono sym) ⟩
  Compatible C₁ F × Compatible (reindex swap C₂) F  ↝⟨ uncurry (Compatible-⊗ mono) ⟩
  Compatible (C₁ ⊗ reindex swap C₂) F               ↔⟨⟩
  Compatible (C₁ ⟷ C₂) F                            □)

------------------------------------------------------------------------
-- Closure properties for Size-preserving

-- The function flip Size-preserving F is closed under reindex,
-- assuming that F is f-symmetric for an involutory function f.
--
-- Note that the assumptions are different from the ones asked for in
-- Compatible-reindex: monotonicity of F has been replaced by the
-- assumption that f is an involution.

Size-preserving-reindex :
  ∀ {ℓ} {I : Set ℓ} {C : Container I I} {F : Trans ℓ I} {f : I → I} →
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

-- Three negative results:
--
-- * The function flip Size-preserving F is not closed under _⟷_, not
--   even if F is monotone and symmetric.
--
-- * In fact, it is not in general the case that a monotone and
--   symmetric function F that is size-preserving for similarity for
--   CCS is also size-preserving for bisimilarity for CCS.
--
-- * Furthermore flip Size-preserving F is not closed under _⊗_, not
--   even if F is monotone.

¬-Size-preserving-⟷/⊗ :
  ¬ ({I : Set} {C₁ C₂ : Container (I × I) (I × I)}
     {F : Trans₂ (# 0) I} →
     Monotone F → Symmetric swap F →
     Size-preserving C₁ F → Size-preserving C₂ F →
     Size-preserving (C₁ ⟷ C₂) F)
    ×
  ¬ ({F : Trans₂ (# 0) Proc} →
     Monotone F → Symmetric swap F →
     Size-preserving S.S̲t̲e̲p̲ F →
     Size-preserving B.S̲t̲e̲p̲ F)
    ×
  ¬ ({I : Set} {C₁ C₂ : Container I I} {F : Trans (# 0) I} →
     Monotone F →
     Size-preserving C₁ F → Size-preserving C₂ F →
     Size-preserving (C₁ ⊗ C₂) F)
¬-Size-preserving-⟷/⊗ =

    (({I : Set} {C₁ C₂ : Container (I × I) (I × I)}
      {F : Trans₂ (# 0) I} →
      Monotone F → Symmetric swap F →
      Size-preserving C₁ F → Size-preserving C₂ F →
      Size-preserving (C₁ ⟷ C₂) F)                   ↝⟨ (λ closed mono symm pres → closed mono symm pres pres) ⟩

     ({F : Trans₂ (# 0) Proc} →
      Monotone F → Symmetric swap F →
      Size-preserving S.S̲t̲e̲p̲ F →
      Size-preserving B.S̲t̲e̲p̲ F)                      ↝⟨ contradiction₂ ⟩□

     ⊥                                               □)

  , contradiction₂

  , (({I : Set} {C₁ C₂ : Container I I}
      {F : Trans (# 0) I} →
      Monotone F →
      Size-preserving C₁ F → Size-preserving C₂ F →
      Size-preserving (C₁ ⊗ C₂) F)                   ↝⟨ (λ closed → closed mono pres) ⟩

     (Size-preserving (reindex swap S.S̲t̲e̲p̲) F →
      Size-preserving B.S̲t̲e̲p̲ F)                      ↝⟨ _$ Size-preserving-reindex refl symm pres ⟩

     Size-preserving B.S̲t̲e̲p̲ F                        ↝⟨ contradiction ⟩□

     ⊥                                               □)

  where
  ≤≥≁ = SC.≤≥≁ tt

  m₁ = proj₁ ≤≥≁
  m₂ = proj₁ (proj₂ ≤≥≁)

  F : Trans₂ (# 0) Proc
  F R = R ∪ (_≡ (m₁ , m₂)) ∪ (_≡ (m₂ , m₁))

  mono : Monotone F
  mono R⊆S = ⊎-map R⊆S id

  symm : Symmetric swap F
  symm R =
    F (R ∘ swap)                                              ⊆⟨⟩
    R ∘ swap ∪ (_≡ (m₁ , m₂))        ∪ (_≡ (m₂ , m₁))         ⊆⟨ ⊎-map id P.[ inj₂ ∘ lemma , inj₁ ∘ lemma ] ⟩
    R ∘ swap ∪ (_≡ (m₁ , m₂)) ∘ swap ∪ (_≡ (m₂ , m₁)) ∘ swap  ⊆⟨ id ⟩∎
    F R ∘ swap                                                ∎
    where
    lemma : {p₁ p₂ : Proc × Proc} → p₁ ≡ swap p₂ → swap p₁ ≡ p₂
    lemma refl = refl

  pres : Size-preserving S.S̲t̲e̲p̲ F
  pres {R = R} {i = i} R⊆ =
    F R                                  ⊆⟨⟩
    R ∪ (_≡ (m₁ , m₂)) ∪ (_≡ (m₂ , m₁))  ⊆⟨ [ R⊆ , helper ] ⟩∎
    Similarity i                         ∎
    where
    helper : ∀ {p} → p ≡ (m₁ , m₂) ⊎ p ≡ (m₂ , m₁) → Similarity i p
    helper (inj₁ refl) = proj₁ (proj₂ (proj₂ ≤≥≁))
    helper (inj₂ refl) = proj₁ (proj₂ (proj₂ (proj₂ ≤≥≁)))

  contradiction =
    Size-preserving B.S̲t̲e̲p̲ F             ↝⟨ (λ hyp → _⇔_.to (monotone→⇔ _ mono) hyp) ⟩
    F (Bisimilarity ∞) ⊆ Bisimilarity ∞  ↝⟨ _$ inj₂ (inj₁ refl) ⟩
    m₁ ∼ m₂                              ↝⟨ proj₂ (proj₂ (proj₂ (proj₂ ≤≥≁))) ⟩□
    ⊥                                    □

  contradiction₂ =
    ({F : Trans₂ (# 0) Proc} →
     Monotone F → Symmetric swap F →
     Size-preserving S.S̲t̲e̲p̲ F →
     Size-preserving B.S̲t̲e̲p̲ F)        ↝⟨ (λ closed → closed mono symm pres) ⟩

    Size-preserving B.S̲t̲e̲p̲ F          ↝⟨ contradiction ⟩□

    ⊥                                 □
