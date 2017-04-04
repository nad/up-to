------------------------------------------------------------------------
-- Up-to techniques for the delay monad
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Bisimilarity.Up-to.Delay-monad {A : Set} where

open import Delay-monad
import Delay-monad.Partial-order as P
import Delay-monad.Weak-bisimilarity as W
open import Equality.Propositional
open import Logical-equivalence using (_⇔_)
open import Prelude

open import Double-negation equality-with-J
open import Function-universe equality-with-J hiding (id)
open import H-level equality-with-J

open import Equational-reasoning
open import Labelled-transition-system

open Labelled-transition-system.Delay-monad A
open LTS delay-monad hiding (_[_]⟶_)

open import Bisimilarity.Classical (weak delay-monad)
  using (Progression)
open import Bisimilarity.Classical.Preliminaries
open import Bisimilarity.Up-to (weak delay-monad)
open import Bisimilarity.Weak.Coinductive delay-monad
import Bisimilarity.Weak.Coinductive.Equational-reasoning-instances
open import Bisimilarity.Weak.Coinductive.Equivalent
import Bisimilarity.Weak.Coinductive.Other delay-monad as CWO
import Bisimilarity.Weak.Delay-monad as W′

-- Everything is an up-to technique for weak bisimilarity for the
-- delay monad (if A is a set, and assuming excluded middle).

everything-up-to :
  ∀ {ℓ} →
  Excluded-middle lzero →
  Is-set A →
  (F : Trans ℓ (Delay A ∞)) →
  Up-to-technique F
everything-up-to {ℓ} em A-set F R R-prog = everything-up-to′
  where
  lemma :
    ∀ {x y} {P : Rel ℓ (Delay A ∞)} →
    (∀ {x′ z} → x [ just z ]⇒̂ x′ →
     ∃ λ y′ → y [ just z ]⇒̂ y′ × P x′ y′) →
    (∃ λ z → now z W.≈ x) →
    x ≈ y
  lemma {x} {y} hyp = uncurry λ z →
    now z W.≈ x                              ↝⟨ _⇔_.to W′.direct⇔indirect′ ⟩
    now z ≈ x                                ↝⟨ (λ nz≈x → Σ-map id proj₁ $ left-to-right nz≈x (⟶→⇒̂ now⟶)) ⟩
    ∃ (x [ just z ]⇒̂_)                       ↝⟨ (λ x⇒̂ → x⇒̂ , Σ-map id proj₁ (hyp (proj₂ x⇒̂))) ⟩
    ∃ (x [ just z ]⇒̂_) × ∃ (y [ just z ]⇒̂_)  ↝⟨ (uncurry λ x⇒̂ y⇒̂ → W′.⇒̂-with-equal-labels→≈ id (proj₂ x⇒̂) (proj₂ y⇒̂)) ⟩
    x CWO.≈ y                                ↝⟨ cwo⇒cw ⟩□
    x ≈ y                                    □

  everything-up-to′ : ∀ x y → R x y → x ≈ y
  everything-up-to′ x y Rxy with P.⇑⊎⇓ em A-set x | P.⇑⊎⇓ em A-set y
  ... | inj₂ x⇓ | _       = lemma (Progression.left-to-right
                                     R-prog Rxy) x⇓
  ... | _       | inj₂ y⇓ = symmetric
                              (lemma (Progression.right-to-left
                                        R-prog Rxy) y⇓)
  ... | inj₁ x⇑ | inj₁ y⇑ =
    x      ∼⟨ symmetric (_⇔_.to W′.direct⇔indirect′ x⇑) ⟩
    never  ∼⟨ _⇔_.to W′.direct⇔indirect′ y⇑ ⟩■
    y
