------------------------------------------------------------------------
-- Examples/exercises related to CCS from "Enhancements of the
-- bisimulation proof method" by Pous and Sangiorgi
--
-- Implemented using coinductive definitions of strong and weak
-- bisimilarity and expansion.
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Bisimilarity.Weak.CCS.Examples {Name : Set} where

open import Equality.Propositional
open import Prelude hiding (module W)

open import Function-universe equality-with-J hiding (id; _∘_)

import Bisimilarity.Coinductive.Equational-reasoning-instances
open import Bisimilarity.Exercises.Coinductive.CCS
import Bisimilarity.Weak.CCS as WL
import
  Bisimilarity.Weak.Coinductive.Other.Equational-reasoning-instances
open import Equational-reasoning
import Expansion.CCS as EL
import Expansion.Equational-reasoning-instances
open import Labelled-transition-system.CCS Name

open import Bisimilarity.Coinductive CCS as S using (_∼_; _∼′_; ∼:_)
open import Bisimilarity.Weak.Coinductive.Other CCS as W
open import Expansion CCS as E
import Labelled-transition-system.Equational-reasoning-instances CCS

mutual

  -- Example 6.5.4.

  6-5-4 :
    ∀ {i a b} →
    [ i ] ! name a · (b ·) ∣ ! co a · ≈ (! a · ∣ ! b ·) ∣ ! co a ·
  6-5-4 {i} {a} {b} = W.⟨ lr , rl ⟩
    where
    lemma =
      (! a · ∣ ! b ·) ∣ b ·  ∼⟨ symmetric ∣-assoc ⟩
      ! a · ∣ (! b · ∣ b ·)  ∼⟨ symmetric ∣-right-identity ∣-cong 6-1-2 ⟩■
      (! a · ∣ ∅) ∣ ! b ·

    lr :
      ∀ {P μ} →
      ! name a · (b ·) ∣ ! co a · [ μ ]⟶ P →
      ∃ λ Q → (! a · ∣ ! b ·) ∣ ! co a · [ μ ]⇒̂ Q × [ i ] P ≈′ Q
    lr (par-left {P′ = P} tr) = case 6-1-3-2 tr of λ where
      (inj₁ (.(b ·) , action , P∼!ab∣b)) →
        P ∣ ! co a ·                         ∼⟨ P∼!ab∣b ∣-cong reflexive ⟩
        (! name a · (b ·) ∣ b ·) ∣ ! co a ·  ∼⟨ swap-rightmost ⟩
        (! name a · (b ·) ∣ ! co a ·) ∣ b ·  ∼′⟨ 6-5-4′ WL.∣-cong′ reflexive ⟩
        ((! a · ∣ ! b ·) ∣ ! co a ·) ∣ b ·   ∼⟨ swap-rightmost ⟩ ∼:
        ((! a · ∣ ! b ·) ∣ b ·) ∣ ! co a ·   ∼⟨ lemma ∣-cong reflexive ⟩■
        ((! a · ∣ ∅) ∣ ! b ·) ∣ ! co a ·
          W.⇐̂[ name a ]                      ←⟨ par-left (par-left (replication (par-right action))) ⟩■
        (! a · ∣ ! b ·) ∣ ! co a ·

      (inj₂ (_ , .(b ·) , _ , .a , action , ab[a̅]⟶ , _)) →
        ⊥-elim (names-are-not-inverted ab[a̅]⟶)

    lr (par-right {Q′ = Q} tr) = case 6-1-3-2 tr of λ where
      (inj₁ (.∅ , action , Q∼!a̅∣∅)) →
        ! name a · (b ·) ∣ Q               ∼⟨ reflexive ∣-cong Q∼!a̅∣∅ ⟩
        ! name a · (b ·) ∣ (! co a · ∣ ∅)  ∼⟨ ∣-assoc ⟩
        (! name a · (b ·) ∣ ! co a ·) ∣ ∅  ∼′⟨ 6-5-4′ WL.∣-cong′ reflexive ⟩ ∼:
        ((! a · ∣ ! b ·) ∣ ! co a ·) ∣ ∅   ∼⟨ symmetric ∣-assoc ⟩■
        (! a · ∣ ! b ·) ∣ (! co a · ∣ ∅)
          W.⇐̂[ name (co a) ]               ←⟨ par-right (replication (par-right action)) ⟩■
        (! a · ∣ ! b ·) ∣ ! co a ·

      (inj₂ (_ , .∅ , _ , .(co a) , action , a̅[a̅̅]⟶ , _)) →
        ⊥-elim (names-are-not-inverted a̅[a̅̅]⟶)

    lr (par-τ′ {P′ = P} {Q′ = Q} _ tr₁ tr₂) =
      case 6-1-3-2 tr₁ ,′ 6-1-3-2 tr₂ of λ where
        (inj₁ (.(b ·) , action , P∼!ab∣b) ,
         inj₁ (.∅     , action , Q∼!a̅∣∅)) →
          P ∣ Q                                      ∼⟨ P∼!ab∣b ∣-cong Q∼!a̅∣∅ ⟩
          (! name a · (b ·) ∣ b ·) ∣ (! co a · ∣ ∅)  ∼⟨ swap-in-the-middle ⟩
          (! name a · (b ·) ∣ ! co a ·) ∣ (b · ∣ ∅)  ∼′⟨ 6-5-4′ WL.∣-cong′ reflexive ⟩
          ((! a · ∣ ! b ·) ∣ ! co a ·) ∣ (b · ∣ ∅)   ∼⟨ swap-in-the-middle ⟩ ∼:
          ((! a · ∣ ! b ·) ∣ b ·) ∣ (! co a · ∣ ∅)   ∼⟨ lemma ∣-cong reflexive ⟩■
          ((! a · ∣ ∅) ∣ ! b ·) ∣ (! co a · ∣ ∅)
            W.⇐̂[ τ ]                                 ←⟨ par-τ (par-left (replication (par-right action)))
                                                              (replication (par-right action)) ⟩■
          (! a · ∣ ! b ·) ∣ ! co a ·

        (_ , inj₂ (() , _))
        (inj₂ (() , _) , _)

    rl-lemma :
      ∀ {Q μ} →
      (! a · ∣ ! b ·) ∣ ! co a · [ μ ]⟶ Q →
      (! a · ∣ ! b ·) ∣ ! co a · ∼ Q
        ×
      (μ ≡ name a ⊎ μ ≡ name b ⊎ μ ≡ name (co a) ⊎ μ ≡ τ)
    rl-lemma (par-left (par-left {P′ = P} tr)) =
      case 6-1-3-2 tr of λ where
        (inj₁ (.∅ , action , P∼!a∣∅)) →
            ((! a · ∣ ! b ·) ∣ ! co a ·        ∼⟨ (symmetric ∣-right-identity ∣-cong reflexive) ∣-cong reflexive ⟩
             ((! a · ∣ ∅) ∣ ! b ·) ∣ ! co a ·  ∼⟨ (symmetric P∼!a∣∅ ∣-cong reflexive) ∣-cong reflexive ⟩■
             (P ∣ ! b ·) ∣ ! co a ·)
          , inj₁ refl

        (inj₂ (refl , .∅ , _ , .a , action , a[a̅]⟶ , _)) →
          ⊥-elim (names-are-not-inverted a[a̅]⟶)

    rl-lemma (par-left (par-right {Q′ = P} tr)) =
      case 6-1-3-2 tr of λ where
        (inj₁ (.∅ , action , P∼!b∣∅)) →
            ((! a · ∣ ! b ·) ∣ ! co a ·        ∼⟨ (reflexive ∣-cong symmetric ∣-right-identity) ∣-cong reflexive ⟩
             (! a · ∣ (! b · ∣ ∅)) ∣ ! co a ·  ∼⟨ (reflexive ∣-cong symmetric P∼!b∣∅) ∣-cong reflexive ⟩■
             (! a · ∣ P) ∣ ! co a ·)
          , inj₂ (inj₁ refl)

        (inj₂ (_ , .∅ , _ , .b , action , b[b̅]⟶ , _)) →
          ⊥-elim (names-are-not-inverted b[b̅]⟶)

    rl-lemma (par-left (par-τ′ {P′ = P} {Q′ = Q} _ tr₁ tr₂)) =
      case 6-1-3-2 tr₁ ,′ 6-1-3-2 tr₂ of λ where
        (inj₁ (.∅ , action , P∼!a∣∅) ,
         inj₁ (.∅ , action , Q∼!b∣∅)) →
            ((! a · ∣ ! b ·) ∣ ! co a ·              ∼⟨ symmetric (∣-right-identity ∣-cong ∣-right-identity) ∣-cong reflexive ⟩
             ((! a · ∣ ∅) ∣ (! b · ∣ ∅)) ∣ ! co a ·  ∼⟨ symmetric (P∼!a∣∅ ∣-cong Q∼!b∣∅) ∣-cong reflexive ⟩■
             (P ∣ Q) ∣ ! co a ·)
          , inj₂ (inj₂ (inj₂ refl))

        (inj₂ (() , _) , _)
        (_ , inj₂ (() , _))

    rl-lemma (par-right {Q′ = Q} tr) =
      case 6-1-3-2 tr of λ where
        (inj₁ (.∅ , action , Q∼!a̅∣∅)) →
            ((! a · ∣ ! b ·) ∣ ! co a ·        ∼⟨ reflexive ∣-cong symmetric ∣-right-identity ⟩
             (! a · ∣ ! b ·) ∣ (! co a · ∣ ∅)  ∼⟨ reflexive ∣-cong symmetric Q∼!a̅∣∅ ⟩■
             (! a · ∣ ! b ·) ∣ Q)
          , inj₂ (inj₂ (inj₁ refl))

        (inj₂ (_ , .∅ , _ , .(co a) , action , a̅[a̅̅]⟶ , _)) →
          ⊥-elim (names-are-not-inverted a̅[a̅̅]⟶)

    rl-lemma (par-τ′ {Q′ = Q} _ (par-left {P′ = P} tr₁) tr₂) =
      case 6-1-3-2 tr₁ ,′ 6-1-3-2 tr₂ of λ where
        (inj₁ (.∅ , action , P∼!a∣∅) ,
         inj₁ (.∅ , action , Q∼!a̅∣∅)) →
            ((! a · ∣ ! b ·) ∣ ! co a ·              ∼⟨ symmetric ((∣-right-identity ∣-cong reflexive) ∣-cong ∣-right-identity) ⟩
             ((! a · ∣ ∅) ∣ ! b ·) ∣ (! co a · ∣ ∅)  ∼⟨ symmetric ((P∼!a∣∅ ∣-cong reflexive) ∣-cong Q∼!a̅∣∅) ⟩■
             (P ∣ ! b ·) ∣ Q)
          , inj₂ (inj₂ (inj₂ refl))

        (inj₂ (() , _) , _)
        (_ , inj₂ (() , _))

    rl-lemma (par-τ′ {Q′ = Q} _ (par-right {Q′ = P} tr₁) tr₂) =
      case 6-1-3-2 tr₁ ,′ 6-1-3-2 tr₂ of λ where
        (inj₁ (.∅ , action , P∼!b∣∅) ,
         inj₁ (.∅ , action , Q∼!a̅∣∅)) →
            ((! a · ∣ ! b ·) ∣ ! co a ·              ∼⟨ symmetric ((reflexive ∣-cong ∣-right-identity) ∣-cong ∣-right-identity) ⟩
             (! a · ∣ (! b · ∣ ∅)) ∣ (! co a · ∣ ∅)  ∼⟨ symmetric ((reflexive ∣-cong P∼!b∣∅) ∣-cong Q∼!a̅∣∅) ⟩■
             (! a · ∣ P) ∣ Q)
          , inj₂ (inj₂ (inj₂ refl))

        (inj₂ (() , _) , _)
        (_ , inj₂ (() , _))

    rl :
      ∀ {Q μ} →
      (! a · ∣ ! b ·) ∣ ! co a · [ μ ]⟶ Q →
      ∃ λ P → ! name a · (b ·) ∣ ! co a · [ μ ]⇒̂ P × [ i ] P ≈′ Q
    rl {Q} tr = case rl-lemma tr of λ where
      (!a∣!b∣!a̅∼Q , inj₁ refl) →
        ! name a · (b ·) ∣ ! co a ·          →⟨ par-left (replication (par-right action)) ⟩■
          W.⇒̂[ name a ]
        (! name a · (b ·) ∣ b ·) ∣ ! co a ·  ∼⟨ swap-rightmost ⟩
        (! name a · (b ·) ∣ ! co a ·) ∣ b ·  ∼′⟨ 6-5-4′ WL.∣-cong′ reflexive ⟩
        ((! a · ∣ ! b ·) ∣ ! co a ·) ∣ b ·   ∼⟨ swap-rightmost ⟩
        ((! a · ∣ ! b ·) ∣ b ·) ∣ ! co a ·   ∼⟨ symmetric ∣-assoc ∣-cong reflexive ⟩
        (! a · ∣ (! b · ∣ b ·)) ∣ ! co a ·   ∼⟨ (reflexive ∣-cong 6-1-2) ∣-cong reflexive ⟩ ∼:
        (! a · ∣ ! b ·) ∣ ! co a ·           ∼⟨ !a∣!b∣!a̅∼Q ⟩■
        Q

      (!a∣!b∣!a̅∼Q , inj₂ (inj₁ refl)) →
        ! name a · (b ·) ∣ ! co a ·                  →⟨ par-τ (replication (par-right action))
                                                              (replication (par-right action)) ⟩
        (! name a · (b ·) ∣ (b ·)) ∣ (! co a · ∣ ∅)  →⟨ par-left (par-right action) ⟩■
          W.⇒̂[ name b ]
        (! name a · (b ·) ∣ ∅) ∣ (! co a · ∣ ∅)      ∼⟨ ∣-right-identity ∣-cong ∣-right-identity ⟩
        (! name a · (b ·)) ∣ ! co a ·                ∼′⟨ 6-5-4′ ⟩ ∼:
        (! a · ∣ ! b ·) ∣ ! co a ·                   ∼⟨ !a∣!b∣!a̅∼Q ⟩■
        Q

      (!a∣!b∣!a̅∼Q , inj₂ (inj₂ (inj₁ refl))) →
        ! name a · (b ·) ∣ ! co a ·        →⟨ par-right (replication (par-right action)) ⟩■
          W.⇒̂[ name (co a) ]
        ! name a · (b ·) ∣ (! co a · ∣ ∅)  ∼⟨ reflexive ∣-cong ∣-right-identity ⟩
        ! name a · (b ·) ∣ ! co a ·        ∼′⟨ 6-5-4′ ⟩ ∼:
        (! a · ∣ ! b ·) ∣ ! co a ·         ∼⟨ !a∣!b∣!a̅∼Q ⟩■
        Q

      (!a∣!b∣!a̅∼Q , inj₂ (inj₂ (inj₂ refl))) →
        ! name a · (b ·) ∣ ! co a ·  ■
          W.⇒̂[ τ ]
        ! name a · (b ·) ∣ ! co a ·  ∼′⟨ 6-5-4′ ⟩ ∼:
        (! a · ∣ ! b ·) ∣ ! co a ·   ∼⟨ !a∣!b∣!a̅∼Q ⟩■
        Q

  6-5-4′ :
    ∀ {i a b} →
    [ i ] ! name a · (b ·) ∣ ! co a · ≈′ (! a · ∣ ! b ·) ∣ ! co a ·
  force 6-5-4′ = 6-5-4

-- The first part of Exercise 6.5.8.

6-5-8-1 :
  ∀ a {P Q} →
  ν (proj₁ a) (name a · P ∣ name (co a) · Q) ≳ ν (proj₁ a) (P ∣ Q)
6-5-8-1 a {P} {Q} = E.⟨ lr , rl ⟩
  where
  lr :
    ∀ {μ R} →
    ν (proj₁ a) (name a · P ∣ name (co a) · Q) [ μ ]⟶ R →
    ∃ λ R′ → ν (proj₁ a) (P ∣ Q) [ μ ]⟶̂ R′ × R ≳′ R′
  lr (restriction a∉μ (par-left action))        = ⊥-elim (a∉μ refl)
  lr (restriction a∉μ (par-right action))       = ⊥-elim (a∉μ refl)
  lr (restriction a∉μ (par-τ′ _ action action)) =
    ν (proj₁ a) (P ∣ Q)  ■
      ⟵̂[ τ ]
    ν (proj₁ a) (P ∣ Q)  ■

  rl :
    ∀ {μ R′} →
    ν (proj₁ a) (P ∣ Q) [ μ ]⟶ R′ →
    ∃ λ R → ν (proj₁ a) (name a · P ∣ name (co a) · Q) [ μ ]⇒̂ R ×
            R ≳′ R′
  rl {μ} (restriction {P′ = R} a∉μ P∣Q⟶R) =
    ν (proj₁ a) (name a · P ∣ name (co a) · Q)  →⟨ restriction _ (par-τ action action) ⟩
    ν (proj₁ a) (P ∣ Q)                         →⟨ restriction a∉μ P∣Q⟶R ⟩■
      E.⇒̂[ μ ]
    ν (proj₁ a) R                               ■

-- One interpretation of the second part of Exercise 6.5.8 is
-- contradictory, assuming that Name is inhabited.

¬-6-5-8-2 :
  Name →
  ¬ (∀ {a b P} →
     ! ν (proj₁ a) (name b · (a ·) ∣ name (co a) · P) ≈
     ! name b · ν (proj₁ a) P)
¬-6-5-8-2 x =
  (∀ {a b P} →
   ! ν (proj₁ a) (name b · (a ·) ∣ name (co a) · P) ≈
   ! name b · ν (proj₁ a) P)                                            ↝⟨ (λ hyp → hyp {_}) ⟩

  (! ν (proj₁ a) (name a · (a ·) ∣ co a ·) ≈ ! name a · ν (proj₁ a) ∅)  ↝⟨ (λ hyp → Σ-map id proj₁ $ W.right-to-left hyp
                                                                                                       (replication (par-right action))) ⟩
  ∃ (! ν (proj₁ a) (name a · (a ·) ∣ co a ·) [ name a ]⇒̂_)              ↝⟨ !P₁⇒̂ ∘ proj₂ ⟩□

  ⊥                                                                     □
  where
  a = x , true

  P₁ = ν (proj₁ a) (name a · (a ·) ∣ co a ·)
  P₂ = ν (proj₁ a) (a · ∣ ∅)

  P₁⟶ : ∀ {μ P} → P₁ [ μ ]⟶ P → τ ≡ μ × P ≡ P₂
  P₁⟶ (restriction a≢a (par-left action))        = ⊥-elim (a≢a refl)
  P₁⟶ (restriction a≢a (par-right action))       = ⊥-elim (a≢a refl)
  P₁⟶ (restriction _   (par-τ′ _ action action)) = refl , refl

  P₂⟶ : ∀ {μ P} → ¬ P₂ [ μ ]⟶ P
  P₂⟶ (restriction a≢a (par-left action))    = ⊥-elim (a≢a refl)
  P₂⟶ (restriction _   (par-right ()))
  P₂⟶ (restriction _   (par-τ′ _ action ()))

  !P₁⟶ : ∀ {μ Q} → ! P₁ [ μ ]⟶ Q → τ ≡ μ × Q ∼ ! P₁ ∣ P₂
  !P₁⟶ (replication (par-left {P′ = Q} tr)) =
    flip (Σ-map id) (!P₁⟶ tr) λ Q∼ →
      Q ∣ P₁            ∼⟨ Q∼ ∣-cong (_ ■) ⟩
      (! P₁ ∣ P₂) ∣ P₁  ∼⟨ swap-rightmost ⟩
      (! P₁ ∣ P₁) ∣ P₂  ∼⟨ 6-1-2 ∣-cong (_ ■) ⟩■
      ! P₁ ∣ P₂

  !P₁⟶ (replication (par-right {Q′ = Q} tr)) =
    flip (Σ-map id) (P₁⟶ tr) λ Q≡ →
      ! P₁ ∣ Q  ∼≡⟨ cong (_ ∣_) Q≡ ⟩■
      ! P₁ ∣ P₂

  !P₁⟶ (replication (par-τ tr₁ tr₂)) = ⊥-elim (
                      $⟨ tr₂ ⟩
    P₁ [ name _ ]⟶ _  ↝⟨ proj₁ ∘ P₁⟶ ⟩
    τ ≡ name _        ↝⟨ name≢τ ∘ sym ⟩□
    ⊥                 □)

  P₂∣P₂∼P₂ : P₂ ∣ P₂ ∼ P₂
  P₂∣P₂∼P₂ =
    S.⟨ (λ where
           (par-left  tr) → ⊥-elim (P₂⟶ tr)
           (par-right tr) → ⊥-elim (P₂⟶ tr)
           (par-τ _   tr) → ⊥-elim (P₂⟶ tr))
      , ⊥-elim ∘ P₂⟶
      ⟩

  !P₁∣P₂⟶ : ∀ {μ Q} → ! P₁ ∣ P₂ [ μ ]⟶ Q → τ ≡ μ × Q ∼ ! P₁ ∣ P₂
  !P₁∣P₂⟶ (par-left {P′ = Q} tr) =
    flip (Σ-map id) (!P₁⟶ tr) λ Q∼ →
      Q ∣ P₂            ∼⟨ Q∼ ∣-cong (_ ■) ⟩
      (! P₁ ∣ P₂) ∣ P₂  ∼⟨ symmetric ∣-assoc ⟩
      ! P₁ ∣ (P₂ ∣ P₂)  ∼⟨ (_ ■) ∣-cong P₂∣P₂∼P₂ ⟩■
      ! P₁ ∣ P₂

  !P₁∣P₂⟶ (par-right tr) = ⊥-elim (P₂⟶ tr)
  !P₁∣P₂⟶ (par-τ _ tr)   = ⊥-elim (P₂⟶ tr)

  !P₁∣P₂⇒ : ∀ {Q R} → Q ⇒ R → Q ∼ ! P₁ ∣ P₂ → R ∼ ! P₁ ∣ P₂
  !P₁∣P₂⇒ done                                       = id
  !P₁∣P₂⇒ (step {p = Q} {q = R} {r = S} refl tr trs) =
    Q ∼ ! P₁ ∣ P₂                             ↝⟨ (λ hyp → S.left-to-right hyp tr) ⟩
    (∃ λ R′ → ! P₁ ∣ P₂ [ τ ]⟶ R′ × R ∼′ R′)  ↝⟨ Σ-map id (Σ-map (proj₂ ∘ !P₁∣P₂⟶) id) ⟩
    (∃ λ R′ → R′ ∼ ! P₁ ∣ P₂ × R ∼′ R′)       ↝⟨ (λ { (_ , R′∼ , ∼R′) → transitive ∼R′ R′∼ }) ⟩
    R ∼ ! P₁ ∣ P₂                             ↝⟨ !P₁∣P₂⇒ trs ⟩□
    S ∼ ! P₁ ∣ P₂                             □

  !P₁⇒ : ∀ {Q} → ! P₁ ⇒ Q → Q ∼ ! P₁ ⊎ Q ∼ ! P₁ ∣ P₂
  !P₁⇒ done                                     = inj₁ reflexive
  !P₁⇒ (step {q = Q} {r = R} {μ = μ} _ tr₁ tr₂) = inj₂ (
                           $⟨ tr₁ , tr₂ ⟩
    ! P₁ [ μ ]⟶ Q × Q ⇒ R  ↝⟨ Σ-map (proj₂ ∘ !P₁⟶) id ⟩
    Q ∼ ! P₁ ∣ P₂ × Q ⇒ R  ↝⟨ uncurry (flip !P₁∣P₂⇒) ⟩□
    R ∼ ! P₁ ∣ P₂          □)

  !P₁[]⇒ : ∀ {P} → ¬ ! P₁ [ name a ]⇒ P
  !P₁[]⇒ (steps {p′ = Q} {q′ = R} trs tr _) =           $⟨ trs , tr ⟩
    ! P₁ ⇒ Q × Q [ name a ]⟶ R                          ↝⟨ Σ-map !P₁⇒ id ⟩
    (Q ∼ ! P₁ ⊎ Q ∼ ! P₁ ∣ P₂) × Q [ name a ]⟶ R        ↝⟨ uncurry (flip λ Q⟶ → ⊎-map (λ hyp → Σ-map id proj₁ $ S.left-to-right hyp Q⟶)
                                                                                      (λ hyp → Σ-map id proj₁ $ S.left-to-right hyp Q⟶)) ⟩
    ∃ (! P₁ [ name a ]⟶_) ⊎ ∃ (! P₁ ∣ P₂ [ name a ]⟶_)  ↝⟨ [ proj₁ ∘ !P₁⟶ ∘ proj₂ , proj₁ ∘ !P₁∣P₂⟶ ∘ proj₂ ] ⟩
    τ ≡ name a                                          ↝⟨ name≢τ ∘ sym ⟩□
    ⊥                                                   □

  !P₁⇒̂ : ∀ {P} → ¬ ! P₁ [ name a ]⇒̂ P
  !P₁⇒̂ (silent () _)
  !P₁⇒̂ (non-silent _ tr) = !P₁[]⇒ tr

-- Another interpretation of the second part of Exercise 6.5.8 can be
-- proved.

6-5-8-2 :
  ∀ {i a b P} →
  proj₁ a ≢ proj₁ b →
  [ i ] ! ν (proj₁ a) (name b · (a ·) ∣ name (co a) · P) ≈
        ! name b · ν (proj₁ a) P
6-5-8-2 {i} {a} {b} {P} a≢b = W.⟨ lr , rl ⟩
  where
  6-5-8-2′ :
    [ i ] ! ν (proj₁ a) (name b · (a ·) ∣ name (co a) · P) ≈′
          ! name b · ν (proj₁ a) P
  force 6-5-8-2′ = 6-5-8-2 a≢b

  lr :
    ∀ {Q μ} →
    ! ν (proj₁ a) (name b · (a ·) ∣ name (co a) · P) [ μ ]⟶ Q →
    ∃ λ Q′ → ! name b · ν (proj₁ a) P [ μ ]⇒̂ Q′ × [ i ] Q ≈′ Q′
  lr {Q} tr = case 6-1-3-2 tr of λ where
    (inj₁ (_ , restriction a≢b (par-left action)
             , Q∼!νa[ba∣a̅P]∣νa[a∣a̅P])) →
      Q                                                   ∼⟨ Q∼!νa[ba∣a̅P]∣νa[a∣a̅P] ⟩

      ! ν (proj₁ a) (name b · (a ·) ∣ name (co a) · P) ∣
      ν (proj₁ a) (a · ∣ name (co a) · P)                 ∼⟨ (_ ■) EL.∣-cong 6-5-8-1 _ ⟩

      ! ν (proj₁ a) (name b · (a ·) ∣ name (co a) · P) ∣
      ν (proj₁ a) (∅ ∣ P)                                 ∼⟨ 6-5-8-2′ WL.∣-cong′ convert (ν-cong refl ∣-left-identity) ⟩■

      ! name b · ν (proj₁ a) P ∣ ν (proj₁ a) P

        W.⇐̂[ name b ]                                     ←⟨ replication (par-right action) ⟩■

      ! name b · ν (proj₁ a) P

    (inj₁ (_ , restriction _ (par-τ′ co-a≡co-b action action) , _)) →
      ⊥-elim (             $⟨ co-a≡co-b ⟩
        co a ≡ co b        ↝⟨ cong proj₁ ⟩
        proj₁ a ≡ proj₁ b  ↝⟨ a≢b ⟩□
        ⊥                  □)

    (inj₁ (_ , restriction a≢a (par-right action) , _)) →
      ⊥-elim (a≢a refl)

    (inj₂ (refl , _ , _ , _
                , restriction _ (par-left action)
                , restriction _ (par-left tr)
                , _)) →
      ⊥-elim (names-are-not-inverted tr)

    (inj₂ (refl , _ , _ , _
                , restriction _ (par-right action)
                , restriction _ (par-right tr)
                , _)) →
      ⊥-elim (names-are-not-inverted tr)

    (inj₂ (refl , _ , _ , _
                , restriction a≢b (par-left action)
                , restriction _   (par-right tr)
                , _)) →
                                          $⟨ tr ⟩
      name (co a) · P [ name (co b) ]⟶ _  ↝⟨ cong proj₁ ∘ cancel-name ∘ ·-only ⟩
      proj₁ a ≡ proj₁ b                   ↝⟨ a≢b ⟩
      ⊥                                   ↝⟨ ⊥-elim ⟩□
      _                                   □

    (inj₂ (refl , _ , _ , c
                , restriction a≢c (par-right tr)
                , restriction _   (par-left action)
                , _)) →
                                     $⟨ tr ⟩
      name (co a) · P [ name c ]⟶ _  ↝⟨ cong proj₁ ∘ cancel-name ∘ ·-only ⟩
      proj₁ a ≡ proj₁ c              ↝⟨ a≢c ⟩
      ⊥                              ↝⟨ ⊥-elim ⟩□
      _                              □

  rl :
    ∀ {Q′ μ} →
    ! name b · ν (proj₁ a) P [ μ ]⟶ Q′ →
    ∃ λ Q → ! ν (proj₁ a) (name b · (a ·) ∣ name (co a) · P) [ μ ]⇒̂ Q ×
            [ i ] Q ≈′ Q′
  rl {Q′} tr = case 6-1-3-2 tr of λ where
    (inj₁ (_ , action , Q′∼!bνaP∣νaP)) →
      ! ν (proj₁ a) (name b · (a ·) ∣ name (co a) · P) →⟨ replication (par-right (restriction a≢b (par-left action))) ⟩■

        W.⇒̂[ name b ]

      ! ν (proj₁ a) (name b · (a ·) ∣ name (co a) · P) ∣
      ν (proj₁ a) (a · ∣ name (co a) · P)                 ∼′⟨ 6-5-8-2′ WL.∣-cong′ convert (6-5-8-1 a) ⟩ ∼:

      ! name b · ν (proj₁ a) P ∣ ν (proj₁ a) (∅ ∣ P)      ∼⟨ (_ ■) ∣-cong ν-cong refl ∣-left-identity ⟩

      ! name b · ν (proj₁ a) P ∣ ν (proj₁ a) P            ∼⟨ symmetric Q′∼!bνaP∣νaP ⟩■

      Q′

    (inj₂ (refl , _ , _ , _ , action , tr , _)) →
      ⊥-elim (names-are-not-inverted tr)
