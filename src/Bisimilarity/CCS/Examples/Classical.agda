------------------------------------------------------------------------
-- Some results/examples related to CCS, implemented using the
-- classical definition of bisimilarity
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Bisimilarity.CCS.Examples.Classical {ℓ} {Name : Set ℓ} where

open import Equality.Propositional
open import Prelude

open import Bisimilarity.CCS.Classical
import Bisimilarity.Classical.Equational-reasoning-instances
open import Equational-reasoning
open import Labelled-transition-system.CCS Name
open import Relation

open import Bisimilarity.Classical CCS

------------------------------------------------------------------------
-- Exercise 6.2.4 from "Enhancements of the bisimulation proof method"
-- by Pous and Sangiorgi

6-2-4 : ∀ {a} → ! ! a ∙ ∼ ! a ∙
6-2-4 {a} = bisimulation-up-to-∼⊆∼ R-is base
  where
  data R : Rel₂ ℓ (Proc ∞) where
    base : R (! ! a ∙ , ! a ∙)

  impossible : ∀ {μ P q} {Q : Set q} →
               ! ! a ∙ [ μ ]⟶ P → μ ≡ τ → Q
  impossible {μ} !!a⟶P μ≡τ = ⊥-elim $ name≢τ
    (name a  ≡⟨ !-only (!-only ·-only) !!a⟶P ⟩
     μ       ≡⟨ μ≡τ ⟩∎
     τ       ∎)

  R-is : Bisimulation-up-to-bisimilarity R
  R-is = ⟪ lr , rl ⟫
    where
    lemma = λ {P : Proc ∞} P∼!a∣∅ →
      ! ! a ∙ ∣ P            ∼⟨ reflexive ∣-cong P∼!a∣∅ ⟩
      ! ! a ∙ ∣ (! a ∙ ∣ ∅)  ∼⟨ reflexive ∣-cong ∣-right-identity ⟩
      ! ! a ∙ ∣ ! a ∙        ∼⟨ 6-1-2 ⟩■
      ! ! a ∙

    lr : ∀ {P P′ Q μ} →
         R (P , Q) → P [ μ ]⟶ P′ →
         ∃ λ Q′ → Q [ μ ]⟶ Q′ ×
                  (Bisimilarity ⊙ R ⊙ Bisimilarity) (P′ , Q′)
    lr {P′ = P′} base !!a⟶P′ = case 6-1-3-2 !!a⟶P′ of λ where
      (inj₂ (μ≡τ , _)) → impossible !!a⟶P′ μ≡τ
      (inj₁ (P″ , !a⟶P″ , P′∼!!a∣P″)) → case 6-1-3-2 !a⟶P″ of λ where
        (inj₂ (μ≡τ , _)) → impossible !!a⟶P′ μ≡τ
        (inj₁ (.∅ , action , P″∼!a∣∅)) →
            _
          , (! a ∙      [ name a ]⟶⟨ replication (par-right action) ⟩
             ! a ∙ ∣ ∅)
          , _
          , (P′            ∼⟨ P′∼!!a∣P″ ⟩
             ! ! a ∙ ∣ P″  ∼⟨ ∼: lemma P″∼!a∣∅ ⟩■
             ! ! a ∙)
          , _
          , base
          , (! a ∙      ∼⟨ symmetric ∣-right-identity ⟩■
             ! a ∙ ∣ ∅)

    rl : ∀ {P Q Q′ μ} →
         R (P , Q) → Q [ μ ]⟶ Q′ →
         ∃ λ P′ → P [ μ ]⟶ P′ ×
                  (Bisimilarity ⊙ R ⊙ Bisimilarity) (P′ , Q′)
    rl {Q′ = Q′} base !a⟶Q′ = case 6-1-3-2 !a⟶Q′ of λ where
      (inj₂ (refl , .∅ , Q″ , .a , action , a⟶Q″ , _)) →
        ⊥-elim (names-are-not-inverted a⟶Q″)
      (inj₁ (.∅ , action , Q′∼!a∣∅)) →
          _
        , (! ! a ∙       [ name a ]⟶⟨ replication (par-right !a⟶Q′) ⟩
           ! ! a ∙ ∣ Q′)
        , _
        , (! ! a ∙ ∣ Q′  ∼⟨ lemma Q′∼!a∣∅ ⟩■
           ! ! a ∙)
        , _
        , base
        , (! a ∙      ∼⟨ symmetric ∣-right-identity ⟩
           ! a ∙ ∣ ∅  ∼⟨ symmetric Q′∼!a∣∅ ⟩■
           Q′)

------------------------------------------------------------------------
-- A result mentioned in "Enhancements of the bisimulation proof
-- method" by Pous and Sangiorgi

∙∣∙∼∙∙ : ∀ {a} → a ∙ ∣ a ∙ ∼ name a ∙ (a ∙)
∙∣∙∼∙∙ {a} = bisimulation-up-to-∪⊆∼ R-is base
  where
  data R : Rel₂ ℓ (Proc ∞) where
    base : R (a ∙ ∣ a ∙ , name a ∙ (a ∙))

  R-is : Bisimulation-up-to-∪ R
  R-is = ⟪ lr , rl ⟫
    where
    lr : ∀ {P P′ Q μ} →
         R (P , Q) → P [ μ ]⟶ P′ →
         ∃ λ Q′ → Q [ μ ]⟶ Q′ × (R ∪ Bisimilarity) (P′ , Q′)
    lr base (par-left action) =
        _
      , (name a ∙ (a ∙)  [ name a ]⟶⟨ action ⟩
         a ∙)
      , inj₂ (∅ ∣ a ∙  ∼⟨ ∣-left-identity ⟩■
              a ∙)

    lr base (par-right action) =
        _
      , (name a ∙ (a ∙)  [ name a ]⟶⟨ action ⟩
         a ∙)
      , inj₂ (a ∙ ∣ ∅  ∼⟨ ∣-right-identity ⟩■
              a ∙)

    lr base (par-τ action tr) = ⊥-elim (names-are-not-inverted tr)

    rl : ∀ {P Q Q′ μ} →
         R (P , Q) → Q [ μ ]⟶ Q′ →
         ∃ λ P′ → P [ μ ]⟶ P′ × (R ∪ Bisimilarity) (P′ , Q′)
    rl base action =
        _
      , (a ∙ ∣ a ∙  [ name a ]⟶⟨ par-right action ⟩
         a ∙ ∣ ∅)
      , inj₂ (a ∙ ∣ ∅  ∼⟨ ∣-right-identity ⟩■
              a ∙)
