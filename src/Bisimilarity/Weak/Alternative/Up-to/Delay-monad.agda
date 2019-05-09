------------------------------------------------------------------------
-- Up-to techniques for the delay monad and the alternative
-- coinductive definition of weak bisimilarity
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe --sized-types #-}

module Bisimilarity.Weak.Alternative.Up-to.Delay-monad
         {a} {A : Set a} where

open import Delay-monad
import Delay-monad.Bisimilarity as B
import Delay-monad.Partial-order as P
open import Equality.Propositional as Eq
open import Logical-equivalence using (_⇔_)
open import Prelude
open import Prelude.Size

open import Double-negation equality-with-J
open import Function-universe equality-with-J hiding (id)
open import H-level equality-with-J

import Bisimilarity.Weak.Alternative.Equational-reasoning-instances
import Bisimilarity.Weak.Delay-monad as W′
open import Bisimilarity.Weak.Equivalent
open import Equational-reasoning
open import Labelled-transition-system
open import Labelled-transition-system.Delay-monad A
open import Relation

open import Bisimilarity.Step (weak delay-monad) _[_]⇒̂_ _[_]⇒̂_
open import Bisimilarity.Up-to (weak delay-monad)
import Bisimilarity.Weak delay-monad as BW
open import Bisimilarity.Weak.Alternative delay-monad

-- Everything is an up-to technique for the alternative coinductive
-- definition of weak bisimilarity for the delay monad (if A is a set,
-- and assuming excluded middle and extensionality).

everything-up-to :
  Excluded-middle a →
  Eq.Extensionality a a →
  Is-set A →
  (F : Trans₂ a (Delay A ∞)) →
  Up-to-technique F
everything-up-to em ext A-set F {R = R} R-prog {x = x , y} =
  everything-up-to′ x y
  where
  lemma :
    ∀ {x y} {P : Rel₂ a (Delay A ∞)} →
    (∀ {x′ z} → x [ just z ]⇒̂ x′ →
     ∃ λ y′ → y [ just z ]⇒̂ y′ × P (x′ , y′)) →
    (∃ λ z → now z B.≈ x) →
    x ≈ y
  lemma {x} {y} hyp = uncurry λ z →
    now z B.≈ x                              ↝⟨ _⇔_.to W′.direct⇔alternative ⟩
    now z ≈ x                                ↝⟨ (λ nz≈x → Σ-map id proj₁ $ left-to-right nz≈x (⟶→⇒̂ now)) ⟩
    ∃ (x [ just z ]⇒̂_)                       ↝⟨ (λ x⇒̂ → x⇒̂ , Σ-map id proj₁ (hyp (proj₂ x⇒̂))) ⟩
    ∃ (x [ just z ]⇒̂_) × ∃ (y [ just z ]⇒̂_)  ↝⟨ (uncurry λ x⇒̂ y⇒̂ → W′.⇒̂-with-equal-labels→≈ id (proj₂ x⇒̂) (proj₂ y⇒̂)) ⟩
    x BW.≈ y                                 ↝⟨ ⇒alternative ⟩□
    x ≈ y                                    □

  everything-up-to′ : ∀ x y → R (x , y) → x ≈ y
  everything-up-to′ x y Rxy =
    case P.⇑⊎⇓ em ext A-set x ,′ P.⇑⊎⇓ em ext A-set y of λ where
      (inj₂ x⇓ , _)       → lemma (StepC.left-to-right (R-prog Rxy)) x⇓
      (_       , inj₂ y⇓) → symmetric
                              (lemma (StepC.right-to-left (R-prog Rxy))
                                     y⇓)
      (inj₁ x⇑ , inj₁ y⇑) →
        x      ∼⟨ symmetric (_⇔_.to W′.direct⇔alternative x⇑) ⟩
        never  ∼⟨ _⇔_.to W′.direct⇔alternative y⇑ ⟩■
        y
