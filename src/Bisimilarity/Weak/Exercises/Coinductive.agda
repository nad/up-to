------------------------------------------------------------------------
-- Some exercises and results from "Enhancements of the bisimulation
-- proof method" by Pous and Sangiorgi
--
-- Implemented using the coinductive definitions of strong and weak
-- bisimilarity.
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Bisimilarity.Weak.Exercises.Coinductive where

open import Equality.Propositional
open import Prelude

import Bisimilarity.Coinductive
import
  Bisimilarity.Coinductive.Equational-reasoning-instances
open import Bisimilarity.Exercises.Coinductive
import Bisimilarity.Weak.Coinductive.Other
import
  Bisimilarity.Weak.Coinductive.Other.Equational-reasoning-instances
open import Equational-reasoning
open import Labelled-transition-system

------------------------------------------------------------------------
-- Exercises and results related to CCS

module _ {Name : Set} where

  open CCS Name
  open LTS CCS hiding (Proc; _[_]⟶_)
  open Bisimilarity.Coinductive CCS using (_∼_; ∼:_)
  open Bisimilarity.Weak.Coinductive.Other CCS

  {-# DISPLAY LTS._[_]⟶_ p μ q = p [ μ ]⟶ q #-}
  {-# DISPLAY LTS._[_]⇒̂_ p μ q = p [ μ ]⇒̂ q #-}
  {-# DISPLAY Bisimilarity.Weak.Coinductive.Other.[_]_≈′_ i p q =
              [ i ] p ≈′ q #-}

  ----------------------------------------------------------------------
  -- _∣_ preserves weak bisimilarity

  mutual

    infix 6 _∣-cong-≈_ _∣-cong-≈′_

    _∣-cong-≈_ : ∀ {i P P′ Q Q′} →
                 [ i ] P ≈ P′ → [ i ] Q ≈ Q′ → [ i ] P ∣ Q ≈ P′ ∣ Q′
    _∣-cong-≈_ {i} = λ P≈P′ Q≈Q′ →
      ⟨ lr P≈P′ Q≈Q′
      , Σ-map id (Σ-map id symmetric) ∘
        lr (symmetric P≈P′) (symmetric Q≈Q′)
      ⟩
      where
      lr : ∀ {P P′ Q Q′ R μ} →
           [ i ] P ≈ P′ → [ i ] Q ≈ Q′ → P ∣ Q [ μ ]⟶ R →
           ∃ λ R′ → P′ ∣ Q′ [ μ ]⇒̂ R′ × [ i ] R ≈′ R′
      lr P≈P′ Q≈Q′ (par-left tr)   = Σ-map (_∣ _)
                                           (Σ-map (map-⇒̂ par-left)
                                                  (_∣-cong-≈′
                                                     convert Q≈Q′))
                                       (left-to-right P≈P′ tr)
      lr P≈P′ Q≈Q′ (par-right tr)  = Σ-map (_ ∣_)
                                           (Σ-map (map-⇒̂ par-right)
                                                  (convert P≈P′
                                                     ∣-cong-≈′_))
                                       (left-to-right Q≈Q′ tr)
      lr P≈P′ Q≈Q′ (par-τ tr₁ tr₂) = Σ-zip _∣_
                                           (Σ-zip par-τ-⇒̂ _∣-cong-≈′_)
                                       (left-to-right P≈P′ tr₁)
                                       (left-to-right Q≈Q′ tr₂)

    _∣-cong-≈′_ :
      ∀ {i P P′ Q Q′} →
      [ i ] P ≈′ P′ → [ i ] Q ≈′ Q′ → [ i ] P ∣ Q ≈′ P′ ∣ Q′
    force (P≈′P′ ∣-cong-≈′ Q≈′Q′) = force P≈′P′ ∣-cong-≈ force Q≈′Q′

  ----------------------------------------------------------------------
  -- Example 6.5.4

  mutual

    6-5-4 :
      ∀ {i a b} →
      [ i ] ! name a · (b ·) ∣ ! co a · ≈ (! a · ∣ ! b ·) ∣ ! co a ·
    6-5-4 {i} {a} {b} = ⟨ lr , rl ⟩
      where
      lemma =
        (! a · ∣ ! b ·) ∣ b ·  ∼⟨ symmetric ∣-assoc ⟩
        ! a · ∣ (! b · ∣ b ·)  ∼⟨ symmetric ∣-right-identity ∣-cong 6-1-2 ⟩■
        (! a · ∣ ∅) ∣ ! b ·

      lr :
        ∀ {P μ} →
        ! name a · (b ·) ∣ ! co a · [ μ ]⟶ P →
        ∃ λ Q → (! a · ∣ ! b ·) ∣ ! co a · [ μ ]⇒̂ Q × [ i ] P ≈′ Q
      lr (par-left {P′ = P} tr) with 6-1-3-2 tr
      ... | inj₁ (.(b ·) , action , P∼!ab∣b) =
        P ∣ ! co a ·                         ∼⟨ P∼!ab∣b ∣-cong reflexive ⟩
        (! name a · (b ·) ∣ b ·) ∣ ! co a ·  ∼⟨ swap-rightmost ⟩
        (! name a · (b ·) ∣ ! co a ·) ∣ b ·  ∽⟨ 6-5-4′ ∣-cong-≈′ reflexive ⟩
        ((! a · ∣ ! b ·) ∣ ! co a ·) ∣ b ·   ∼⟨ swap-rightmost ⟩ ∼:
        ((! a · ∣ ! b ·) ∣ b ·) ∣ ! co a ·   ∼⟨ lemma ∣-cong reflexive ⟩■
        ((! a · ∣ ∅) ∣ ! b ·) ∣ ! co a ·     ⟵⟨ par-left (par-left (replication (par-right action))) ⟩⇒̂
        (! a · ∣ ! b ·) ∣ ! co a ·

      ... | inj₂ (_ , .(b ·) , _ , .a , action , ab[a̅]⟶ , _) =
        ⊥-elim (names-are-not-inverted ab[a̅]⟶)

      lr (par-right {Q′ = Q} tr) with 6-1-3-2 tr
      ... | inj₁ (.∅ , action , Q∼!a̅∣∅) =
        ! name a · (b ·) ∣ Q               ∼⟨ reflexive ∣-cong Q∼!a̅∣∅ ⟩
        ! name a · (b ·) ∣ (! co a · ∣ ∅)  ∼⟨ ∣-assoc ⟩
        (! name a · (b ·) ∣ ! co a ·) ∣ ∅  ∽⟨ 6-5-4′ ∣-cong-≈′ reflexive ⟩ ∼:
        ((! a · ∣ ! b ·) ∣ ! co a ·) ∣ ∅   ∼⟨ symmetric ∣-assoc ⟩■
        (! a · ∣ ! b ·) ∣ (! co a · ∣ ∅)   ⟵⟨ par-right (replication (par-right action)) ⟩⇒̂
        (! a · ∣ ! b ·) ∣ ! co a ·

      ... | inj₂ (_ , .∅ , _ , .(co a) , action , a̅[a̅̅]⟶ , _) =
        ⊥-elim (names-are-not-inverted a̅[a̅̅]⟶)

      lr (par-τ′ {P′ = P} {Q′ = Q} _ tr₁ tr₂)
        with 6-1-3-2 tr₁ | 6-1-3-2 tr₂
      ... | inj₁ (.(b ·) , action , P∼!ab∣b)
          | inj₁ (.∅ , action , Q∼!a̅∣∅) =
        P ∣ Q                                      ∼⟨ P∼!ab∣b ∣-cong Q∼!a̅∣∅ ⟩
        (! name a · (b ·) ∣ b ·) ∣ (! co a · ∣ ∅)  ∼⟨ swap-in-the-middle ⟩
        (! name a · (b ·) ∣ ! co a ·) ∣ (b · ∣ ∅)  ∽⟨ 6-5-4′ ∣-cong-≈′ reflexive ⟩
        ((! a · ∣ ! b ·) ∣ ! co a ·) ∣ (b · ∣ ∅)   ∼⟨ swap-in-the-middle ⟩ ∼:
        ((! a · ∣ ! b ·) ∣ b ·) ∣ (! co a · ∣ ∅)   ∼⟨ lemma ∣-cong reflexive ⟩■
        ((! a · ∣ ∅) ∣ ! b ·) ∣ (! co a · ∣ ∅)     [ τ ]⟵⟨ par-τ (par-left (replication (par-right action)))
                                                                 (replication (par-right action)) ⟩⇒̂
        (! a · ∣ ! b ·) ∣ ! co a ·

      ... | _ | inj₂ (() , _)
      ... | inj₂ (() , _) | _

      rl-lemma :
        ∀ {Q μ} →
        (! a · ∣ ! b ·) ∣ ! co a · [ μ ]⟶ Q →
        (! a · ∣ ! b ·) ∣ ! co a · ∼ Q
          ×
        (μ ≡ name a ⊎ μ ≡ name b ⊎ μ ≡ name (co a) ⊎ μ ≡ τ)
      rl-lemma (par-left (par-left {P′ = P} tr)) with 6-1-3-2 tr
      ... | inj₁ (.∅ , action , P∼!a∣∅) =
          ((! a · ∣ ! b ·) ∣ ! co a ·        ∼⟨ (symmetric ∣-right-identity ∣-cong reflexive) ∣-cong reflexive ⟩
           ((! a · ∣ ∅) ∣ ! b ·) ∣ ! co a ·  ∼⟨ (symmetric P∼!a∣∅ ∣-cong reflexive) ∣-cong reflexive ⟩■
           (P ∣ ! b ·) ∣ ! co a ·)
        , inj₁ refl

      ... | inj₂ (refl , .∅ , _ , .a , action , a[a̅]⟶ , _) =
        ⊥-elim (names-are-not-inverted a[a̅]⟶)

      rl-lemma (par-left (par-right {Q′ = P} tr)) with 6-1-3-2 tr
      ... | inj₁ (.∅ , action , P∼!b∣∅) =
          ((! a · ∣ ! b ·) ∣ ! co a ·        ∼⟨ (reflexive ∣-cong symmetric ∣-right-identity) ∣-cong reflexive ⟩
           (! a · ∣ (! b · ∣ ∅)) ∣ ! co a ·  ∼⟨ (reflexive ∣-cong symmetric P∼!b∣∅) ∣-cong reflexive ⟩■
           (! a · ∣ P) ∣ ! co a ·)
        , inj₂ (inj₁ refl)

      ... | inj₂ (_ , .∅ , _ , .b , action , b[b̅]⟶ , _) =
        ⊥-elim (names-are-not-inverted b[b̅]⟶)

      rl-lemma (par-left (par-τ′ {P′ = P} {Q′ = Q} _ tr₁ tr₂))
        with 6-1-3-2 tr₁ | 6-1-3-2 tr₂
      ... | inj₁ (.∅ , action , P∼!a∣∅) | inj₁ (.∅ , action , Q∼!b∣∅) =
          ((! a · ∣ ! b ·) ∣ ! co a ·              ∼⟨ symmetric (∣-right-identity ∣-cong ∣-right-identity) ∣-cong reflexive ⟩
           ((! a · ∣ ∅) ∣ (! b · ∣ ∅)) ∣ ! co a ·  ∼⟨ symmetric (P∼!a∣∅ ∣-cong Q∼!b∣∅) ∣-cong reflexive ⟩■
           (P ∣ Q) ∣ ! co a ·)
        , inj₂ (inj₂ (inj₂ refl))

      ... | inj₂ (() , _) | _
      ... | _ | inj₂ (() , _)

      rl-lemma (par-right {Q′ = Q} tr) with 6-1-3-2 tr
      ... | inj₁ (.∅ , action , Q∼!a̅∣∅) =
          ((! a · ∣ ! b ·) ∣ ! co a ·        ∼⟨ reflexive ∣-cong symmetric ∣-right-identity ⟩
           (! a · ∣ ! b ·) ∣ (! co a · ∣ ∅)  ∼⟨ reflexive ∣-cong symmetric Q∼!a̅∣∅ ⟩■
           (! a · ∣ ! b ·) ∣ Q)
        , inj₂ (inj₂ (inj₁ refl))

      ... | inj₂ (_ , .∅ , _ , .(co a) , action , a̅[a̅̅]⟶ , _) =
        ⊥-elim (names-are-not-inverted a̅[a̅̅]⟶)

      rl-lemma (par-τ′ {Q′ = Q} _ (par-left {P′ = P} tr₁) tr₂)
        with 6-1-3-2 tr₁ | 6-1-3-2 tr₂
      ... | inj₁ (.∅ , action , P∼!a∣∅) | inj₁ (.∅ , action , Q∼!a̅∣∅) =
          ((! a · ∣ ! b ·) ∣ ! co a ·              ∼⟨ symmetric ((∣-right-identity ∣-cong reflexive) ∣-cong ∣-right-identity) ⟩
           ((! a · ∣ ∅) ∣ ! b ·) ∣ (! co a · ∣ ∅)  ∼⟨ symmetric ((P∼!a∣∅ ∣-cong reflexive) ∣-cong Q∼!a̅∣∅) ⟩■
           (P ∣ ! b ·) ∣ Q)
        , inj₂ (inj₂ (inj₂ refl))

      ... | inj₂ (() , _) | _
      ... | _ | inj₂ (() , _)

      rl-lemma (par-τ′ {Q′ = Q} _ (par-right {Q′ = P} tr₁) tr₂)
        with 6-1-3-2 tr₁ | 6-1-3-2 tr₂
      ... | inj₁ (.∅ , action , P∼!b∣∅) | inj₁ (.∅ , action , Q∼!a̅∣∅) =
          ((! a · ∣ ! b ·) ∣ ! co a ·              ∼⟨ symmetric ((reflexive ∣-cong ∣-right-identity) ∣-cong ∣-right-identity) ⟩
           (! a · ∣ (! b · ∣ ∅)) ∣ (! co a · ∣ ∅)  ∼⟨ symmetric ((reflexive ∣-cong P∼!b∣∅) ∣-cong Q∼!a̅∣∅) ⟩■
           (! a · ∣ P) ∣ Q)
        , inj₂ (inj₂ (inj₂ refl))

      ... | inj₂ (() , _) | _
      ... | _ | inj₂ (() , _)

      rl :
        ∀ {Q μ} →
        (! a · ∣ ! b ·) ∣ ! co a · [ μ ]⟶ Q →
        ∃ λ P → ! name a · (b ·) ∣ ! co a · [ μ ]⇒̂ P × [ i ] P ≈′ Q
      rl {Q} tr with rl-lemma tr
      ... | !a∣!b∣!a̅∼Q , inj₁ refl =
        ! name a · (b ·) ∣ ! co a ·          [ name a ]⟶⟨ par-left (replication (par-right action)) ⟩⇒̂
        (! name a · (b ·) ∣ b ·) ∣ ! co a ·  ∼⟨ swap-rightmost ⟩
        (! name a · (b ·) ∣ ! co a ·) ∣ b ·  ∽⟨ 6-5-4′ ∣-cong-≈′ reflexive ⟩
        ((! a · ∣ ! b ·) ∣ ! co a ·) ∣ b ·   ∼⟨ swap-rightmost ⟩
        ((! a · ∣ ! b ·) ∣ b ·) ∣ ! co a ·   ∼⟨ symmetric ∣-assoc ∣-cong reflexive ⟩
        (! a · ∣ (! b · ∣ b ·)) ∣ ! co a ·   ∼⟨ (reflexive ∣-cong 6-1-2) ∣-cong reflexive ⟩ ∼:
        (! a · ∣ ! b ·) ∣ ! co a ·           ∼⟨ !a∣!b∣!a̅∼Q ⟩■
        Q

      -- TODO: Better notation for multiple steps?

      ... | !a∣!b∣!a̅∼Q , inj₂ (inj₁ refl) =
        ! name a · (b ·) ∣ ! co a ·              [ name b ]⇒̂⟨ non-silent (λ ()) (steps (⟶→⇒ refl (par-τ (replication (par-right action))
                                                                                                        (replication (par-right action))))
                                                                                       (par-left (par-right action))
                                                                                       done) ⟩ʳˡ
        (! name a · (b ·) ∣ ∅) ∣ (! co a · ∣ ∅)  ∼⟨ ∣-right-identity ∣-cong ∣-right-identity ⟩
        (! name a · (b ·)) ∣ ! co a ·            ∽⟨ 6-5-4′ ⟩ ∼:
        (! a · ∣ ! b ·) ∣ ! co a ·               ∼⟨ !a∣!b∣!a̅∼Q ⟩■
        Q

      ... | !a∣!b∣!a̅∼Q , inj₂ (inj₂ (inj₁ refl)) =
        ! name a · (b ·) ∣ ! co a ·        [ name (co a) ]⟶⟨ par-right (replication (par-right action)) ⟩⇒̂
        ! name a · (b ·) ∣ (! co a · ∣ ∅)  ∼⟨ reflexive ∣-cong ∣-right-identity ⟩
        ! name a · (b ·) ∣ ! co a ·        ∽⟨ 6-5-4′ ⟩ ∼:
        (! a · ∣ ! b ·) ∣ ! co a ·         ∼⟨ !a∣!b∣!a̅∼Q ⟩■
        Q

      ... | !a∣!b∣!a̅∼Q , inj₂ (inj₂ (inj₂ refl)) =
        ! name a · (b ·) ∣ ! co a ·  [ τ ]⇒̂⟨ silent refl done ⟩ʳˡ
        ! name a · (b ·) ∣ ! co a ·  ∽⟨ 6-5-4′ ⟩ ∼:
        (! a · ∣ ! b ·) ∣ ! co a ·   ∼⟨ !a∣!b∣!a̅∼Q ⟩■
        Q

    6-5-4′ :
      ∀ {i a b} →
      [ i ] ! name a · (b ·) ∣ ! co a · ≈′ (! a · ∣ ! b ·) ∣ ! co a ·
    force 6-5-4′ = 6-5-4
