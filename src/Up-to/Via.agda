------------------------------------------------------------------------
-- Up-to techniques via
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Up-to.Via where

open import Equality.Propositional
open import Logical-equivalence using (_⇔_)
open import Prelude

open import Bijection equality-with-J as Bijection using (_↔_)
open import Function-universe equality-with-J as F hiding (id; _∘_)
open import H-level.Closure equality-with-J using (ext⁻¹)

open import Indexed-container
open import Indexed-container.Combinators
  hiding (id) renaming (_∘_ to _⊚_)
open import Relation
open import Up-to

-- The property of being an up-to technique via another (or the same)
-- relation transformer. This is an adaptation of Definition 6.3.25 in
-- Pous and Sangiorgi's "Enhancements of the bisimulation proof
-- method".

Up-to-technique-via :
  ∀ {ℓ} {I : Set ℓ} →
  Container I I → Trans ℓ I → Trans ℓ I → Set (lsuc ℓ)
Up-to-technique-via C F G =
  Extensive G
    ×
  (∀ R → R ⊆ ⟦ C ⟧ (F R) → G R ⊆ ⟦ C ⟧ (G R))

-- If F is an up-to technique via G, then F is an up-to technique.
--
-- A corresponding result is mentioned by Pous and Sangiorgi right
-- after Definition 6.3.25.

up-to-via→up-to :
  ∀ {ℓ} {I : Set ℓ} {C : Container I I} {F G} →
  Up-to-technique-via C F G → Up-to-technique C F
up-to-via→up-to {C = C} {F} {G} up-to {R} =
  R ⊆ ⟦ C ⟧ (F R)    ↝⟨ proj₂ up-to _ ⟩
  G R ⊆ ⟦ C ⟧ (G R)  ↝⟨ unfold C ⟩
  G R ⊆ ν C ∞        ↝⟨ (λ hyp {_} x → hyp (proj₁ up-to R x)) ⟩□
  R ⊆ ν C ∞          □

-- If F is an up-to technique, then F is an up-to technique via
-- _∪ ν C ∞.

up-to→up-to-via :
  ∀ {ℓ} {I : Set ℓ} {C : Container I I} {F} →
  Up-to-technique C F → Up-to-technique-via C F (_∪ ν C ∞)
up-to→up-to-via {C = C} {F} up-to =
    (λ R →
       R          ⊆⟨ inj₁ ⟩∎
       R ∪ ν C ∞  ∎)
  , λ R →
      R ⊆ ⟦ C ⟧ (F R)                ↝⟨ up-to ⟩
      R ⊆ ν C ∞                      ↝⟨ (λ hyp {_} →

          R ∪ ν C ∞                            ⊆⟨ [ hyp {_} , id ] ⟩
          ν C ∞                                ⊆⟨ ν-out _ ⟩
          ⟦ C ⟧ (ν C ∞)                        ⊆⟨ map C inj₂ ⟩∎
          ⟦ C ⟧ (R ∪ ν C ∞)                    ∎) ⟩

      R ∪ ν C ∞ ⊆ ⟦ C ⟧ (R ∪ ν C ∞)  □

-- A lemma that corresponds to Pous and Sangiorgi's Lemma 6.3.27: If G
-- satisfies certain properties, then Up-to-technique-via C F is
-- closed under G ∘_.

up-to-via-∘ :
  ∀ {ℓ} {I : Set ℓ} {C : Container I I} {F G H} →
  Extensive G →
  (∀ R → R ⊆ ⟦ C ⟧ R → G R ⊆ ⟦ C ⟧ (G R)) →
  Up-to-technique-via C F H →
  Up-to-technique-via C F (G ∘ H)
up-to-via-∘ {C = C} {F} {G} {H} extensive pres up-to =
    (λ R →
       R        ⊆⟨ proj₁ up-to _ ⟩
       H R      ⊆⟨ extensive _ ⟩∎
       G (H R)  ∎)
  , λ R →
      R ⊆ ⟦ C ⟧ (F R)            ↝⟨ proj₂ up-to _ ⟩
      H R ⊆ ⟦ C ⟧ (H R)          ↝⟨ pres _ ⟩□
      G (H R) ⊆ ⟦ C ⟧ (G (H R))  □

mutual

  -- If the container F is an up-to technique via a symmetric relation
  -- transformer, then ν ⟷[ C ⊚ F ] ∞ is contained in ν ⟷[ C ] ∞. This
  -- result corresponds to Pous and Sangiorgi's Proposition 6.3.28.

  up-to-via→ν-∘⊆ν :
    ∀ {ℓ} {I : Set ℓ} {C : Container (I × I) (I × I)} {F G} →
    Symmetric swap G →
    Up-to-technique-via C ⟦ F ⟧ G →
    ν ⟷[ C ⊚ F ] ∞ ⊆ ν ⟷[ C ] ∞
  up-to-via→ν-∘⊆ν symm up-to = up-to-via²→ν-∘⊆ν refl symm up-to up-to

  -- A generalisation of the result above.

  up-to-via²→ν-∘⊆ν :
    ∀ {ℓ} {I : Set ℓ} {C₁ C₂ : Container I I} {F₁ F₂ G} {f : I → I} →
    f ∘ f ≡ id →
    Symmetric f G →
    Up-to-technique-via C₁ ⟦ F₁ ⟧ G →
    Up-to-technique-via C₂ ⟦ F₂ ⟧ G →
    ν (C₁ ⊚ F₁ ⊗ reindex f (C₂ ⊚ F₂)) ∞ ⊆ ν (C₁ ⊗ reindex f C₂) ∞
  up-to-via²→ν-∘⊆ν {ℓ} {I} {C₁} {C₂} {F₁} {F₂} {G} {f}
                   inv symm up-to₁ up-to₂ =
                                                       $⟨ (λ {_} → ν-out _) ⟩
    R ⊆ ⟦ C₁ ⊚ F₁ ⊗ reindex f (C₂ ⊚ F₂) ⟧ R            ↝⟨ ⊆-congʳ _ $ ⟦⊗⟧↔ _ (C₁ ⊚ F₁) (reindex f (C₂ ⊚ F₂)) ⟩
    R ⊆ ⟦ C₁ ⊚ F₁ ⟧ R ∩ ⟦ reindex f (C₂ ⊚ F₂) ⟧ R      ↝⟨ from-isomorphism implicit-ΠΣ-comm F.∘
                                                          implicit-∀-cong _ (from-isomorphism ΠΣ-comm) ⟩
    R ⊆ ⟦ C₁ ⊚ F₁ ⟧ R × R ⊆ ⟦ reindex f (C₂ ⊚ F₂) ⟧ R  ↝⟨ Σ-map lemma₁ lemma₂ ⟩
    G R ⊆ ⟦ C₁ ⟧ (G R) × G R ⊆ ⟦ reindex f C₂ ⟧ (G R)  ↝⟨ _⇔_.from (from-isomorphism implicit-ΠΣ-comm F.∘
                                                                    implicit-∀-cong _ (from-isomorphism ΠΣ-comm)) ⟩
    G R ⊆ ⟦ C₁ ⟧ (G R) ∩ ⟦ reindex f C₂ ⟧ (G R)        ↝⟨ _⇔_.from $ ⊆-congʳ _ $ ⟦⊗⟧↔ _ C₁ (reindex f C₂) ⟩
    G R ⊆ ⟦ C₁ ⊗ reindex f C₂ ⟧ (G R)                  ↝⟨ unfold (C₁ ⊗ reindex f C₂) ⟩
    G R ⊆ ν (C₁ ⊗ reindex f C₂) ∞                      ↝⟨ (λ hyp {_} x → hyp (proj₁ up-to₁ R x)) ⟩□
    R ⊆ ν (C₁ ⊗ reindex f C₂) ∞                        □
    where
    R = ν (C₁ ⊚ F₁ ⊗ reindex f (C₂ ⊚ F₂)) ∞

    I↔I : I ↔ I
    I↔I = Bijection.bijection-from-involutive-family
            (λ _ _ → f) (λ _ _ → ext⁻¹ inv) tt tt

    ∘⊆⇔⊆∘ : {S₁ S₂ : Rel ℓ I} → S₁ ∘ f ⊆ S₂ ⇔ S₁ ⊆ S₂ ∘ f
    ∘⊆⇔⊆∘ {S₁ = S₁} {S₂} =
      (∀ {p} → S₁ (f p) → S₂ p)  ↔⟨ Bijection.implicit-Π↔Π ⟩
      (∀ p → S₁ (f p) → S₂ p)    ↝⟨ Π-cong _ I↔I (λ _ → →-cong _ F.id (≡⇒↝ _ $ cong S₂ $ ext⁻¹ (sym inv) _)) ⟩
      (∀ p → S₁ p → S₂ (f p))    ↔⟨ inverse Bijection.implicit-Π↔Π ⟩□
      (∀ {p} → S₁ p → S₂ (f p))  □

    lemma₁ =
      R ⊆ ⟦ C₁ ⊚ F₁ ⟧ R      ↝⟨ ⊆-congʳ _ (⟦∘⟧↔ _ C₁) ⟩
      R ⊆ ⟦ C₁ ⟧ (⟦ F₁ ⟧ R)  ↝⟨ proj₂ up-to₁ _ ⟩□
      G R ⊆ ⟦ C₁ ⟧ (G R)     □

    lemma₂ =
      R ⊆ ⟦ reindex f (C₂ ⊚ F₂) ⟧ R    ↝⟨ ⊆-congʳ _ $ ⟦reindex⟧↔ _ (C₂ ⊚ F₂) ⟩
      R ⊆ ⟦ C₂ ⊚ F₂ ⟧ (R ∘ f) ∘ f      ↝⟨ ⊆-congʳ _ (⟦∘⟧↔ _ C₂) ⟩
      R ⊆ ⟦ C₂ ⟧ (⟦ F₂ ⟧ (R ∘ f)) ∘ f  ↝⟨ _⇔_.from ∘⊆⇔⊆∘ ⟩
      R ∘ f ⊆ ⟦ C₂ ⟧ (⟦ F₂ ⟧ (R ∘ f))  ↝⟨ proj₂ up-to₂ _ ⟩
      G (R ∘ f) ⊆ ⟦ C₂ ⟧ (G (R ∘ f))   ↝⟨ involution→other-symmetry G inv symm _ ⊆-cong-→ ⟦⟧-cong _ C₂ (symm _) ⟩
      G R ∘ f ⊆ ⟦ C₂ ⟧ (G R ∘ f)       ↝⟨ _⇔_.to ∘⊆⇔⊆∘ ⟩
      G R ⊆ ⟦ C₂ ⟧ (G R ∘ f) ∘ f       ↝⟨ _⇔_.from $ ⊆-congʳ _ $ ⟦reindex⟧↔ _ C₂ ⟩
      G R ⊆ ⟦ reindex f C₂ ⟧ (G R)     □

-- If F is monotone and compatible, then F is an up-to technique via
-- F ^ω_. This result corresponds to Pous and Sangiorgi's
-- Theorem 6.3.26.

compatible→up-to-via :
  ∀ {ℓ} {I : Set ℓ} {C : Container I I} {F} →
  Monotone F →
  Compatible C F → Up-to-technique-via C F (F ^ω_)
compatible→up-to-via {C = C} {F} mono comp =
    (λ R →
       R       ⊆⟨ 0 ,_ ⟩∎
       F ^ω R  ∎)
  , λ R R⊆ →
      F ^ω R          ⊆⟨ compatible→^ω-post-fixpoint _ mono comp R⊆ ⟩∎
      ⟦ C ⟧ (F ^ω R)  ∎
