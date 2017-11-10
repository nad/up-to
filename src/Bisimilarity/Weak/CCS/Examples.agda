------------------------------------------------------------------------
-- Examples/exercises related to CCS from "Enhancements of the
-- bisimulation proof method" by Pous and Sangiorgi
--
-- Implemented using coinductive definitions of strong and weak
-- bisimilarity and expansion.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Bisimilarity.Weak.CCS.Examples {ℓ} {Name : Set ℓ} where

open import Equality.Propositional
open import Prelude hiding (module W)

open import Function-universe equality-with-J hiding (id; _∘_)

import Bisimilarity.Coinductive.Equational-reasoning-instances
open import Bisimilarity.Exercises.Coinductive.CCS
import Bisimilarity.Weak.CCS as WL
import Bisimilarity.Weak.Equational-reasoning-instances
open import Equational-reasoning
import Expansion.CCS as EL
import Expansion.Equational-reasoning-instances
open import Labelled-transition-system.CCS Name

open import Bisimilarity.Coinductive CCS using (_∼_; ∼:_)
open import Bisimilarity.Weak CCS as W
open import Expansion CCS as E
import Labelled-transition-system.Equational-reasoning-instances CCS

mutual

  -- Example 6.5.4.

  6-5-4 :
    ∀ {i a b} →
    [ i ] ! name a ∙ (b ∙) ∣ ! co a ∙ ≈ (! a ∙ ∣ ! b ∙) ∣ ! co a ∙
  6-5-4 {i} {a} {b} = W.⟨ lr , rl ⟩
    where
    lemma =
      (! a ∙ ∣ ! b ∙) ∣ b ∙  ∼⟨ symmetric ∣-assoc ⟩ ∼:
      ! a ∙ ∣ (! b ∙ ∣ b ∙)  ∼⟨ symmetric ∣-right-identity ∣-cong 6-1-2 ⟩■
      (! a ∙ ∣ ∅) ∣ ! b ∙

    lr :
      ∀ {P μ} →
      ! name a ∙ (b ∙) ∣ ! co a ∙ [ μ ]⟶ P →
      ∃ λ Q → (! a ∙ ∣ ! b ∙) ∣ ! co a ∙ [ μ ]⇒̂ Q × [ i ] P ≈′ Q
    lr (par-left {P′ = P} tr) = case 6-1-3-2 tr of λ where
      (inj₁ (.(b ∙) , action , P∼!ab∣b)) →
        P ∣ ! co a ∙                         ∼⟨ P∼!ab∣b ∣-cong reflexive ⟩
        (! name a ∙ (b ∙) ∣ b ∙) ∣ ! co a ∙  ∼⟨ swap-rightmost ⟩
        (! name a ∙ (b ∙) ∣ ! co a ∙) ∣ b ∙  ∼′⟨ 6-5-4′ WL.∣-cong′ reflexive ⟩
        ((! a ∙ ∣ ! b ∙) ∣ ! co a ∙) ∣ b ∙   ∼⟨ swap-rightmost ⟩ ∼:
        ((! a ∙ ∣ ! b ∙) ∣ b ∙) ∣ ! co a ∙   ∼⟨ lemma ∣-cong reflexive ⟩■
        ((! a ∙ ∣ ∅) ∣ ! b ∙) ∣ ! co a ∙
          W.⇐̂[ name a ]                      ←⟨ ⟶: par-left (par-left (replication (par-right action))) ⟩■
        (! a ∙ ∣ ! b ∙) ∣ ! co a ∙

      (inj₂ (_ , .(b ∙) , _ , .a , action , ab[a̅]⟶ , _)) →
        ⊥-elim (names-are-not-inverted ab[a̅]⟶)

    lr (par-right {Q′ = Q} tr) = case 6-1-3-2 tr of λ where
      (inj₁ (.∅ , action , Q∼!a̅∣∅)) →
        ! name a ∙ (b ∙) ∣ Q               ∼⟨ reflexive ∣-cong Q∼!a̅∣∅ ⟩
        ! name a ∙ (b ∙) ∣ (! co a ∙ ∣ ∅)  ∼⟨ ∣-assoc ⟩
        (! name a ∙ (b ∙) ∣ ! co a ∙) ∣ ∅  ∼′⟨ 6-5-4′ WL.∣-cong′ reflexive ⟩ ∼:
        ((! a ∙ ∣ ! b ∙) ∣ ! co a ∙) ∣ ∅   ∼⟨ symmetric ∣-assoc ⟩■
        (! a ∙ ∣ ! b ∙) ∣ (! co a ∙ ∣ ∅)
          W.⇐̂[ name (co a) ]               ←⟨ ⟶: par-right (replication (par-right action)) ⟩■
        (! a ∙ ∣ ! b ∙) ∣ ! co a ∙

      (inj₂ (_ , .∅ , _ , .(co a) , action , a̅[a̅̅]⟶ , _)) →
        ⊥-elim (names-are-not-inverted a̅[a̅̅]⟶)

    lr (par-τ {P′ = P} {Q′ = Q} tr₁ tr₂) =
      case 6-1-3-2 tr₁ ,′ 6-1-3-2 tr₂ of λ where
        (inj₁ (.(b ∙) , action , P∼!ab∣b) ,
         inj₁ (R      , tr     , Q∼!a̅∣R)) →
          P ∣ Q                                      ∼⟨ P∼!ab∣b ∣-cong Q∼!a̅∣R ⟩
          (! name a ∙ (b ∙) ∣ b ∙) ∣ (! co a ∙ ∣ R)  ∼≡⟨ cong (λ R → _ ∣ (_ ∣ R)) (·-only⟶ tr) ⟩
          (! name a ∙ (b ∙) ∣ b ∙) ∣ (! co a ∙ ∣ ∅)  ∼⟨ swap-in-the-middle ⟩
          (! name a ∙ (b ∙) ∣ ! co a ∙) ∣ (b ∙ ∣ ∅)  ∼′⟨ 6-5-4′ WL.∣-cong′ reflexive ⟩
          ((! a ∙ ∣ ! b ∙) ∣ ! co a ∙) ∣ (b ∙ ∣ ∅)   ∼⟨ swap-in-the-middle ⟩ ∼:
          ((! a ∙ ∣ ! b ∙) ∣ b ∙) ∣ (! co a ∙ ∣ ∅)   ∼⟨ lemma ∣-cong reflexive ⟩■
          ((! a ∙ ∣ ∅) ∣ ! b ∙) ∣ (! co a ∙ ∣ ∅)
            W.⇐̂[ τ ]                                 ←⟨ par-τ (par-left (replication (par-right action)))
                                                              (replication (par-right action)) ⟩■
          (! a ∙ ∣ ! b ∙) ∣ ! co a ∙

        (_ , inj₂ (() , _))
        (inj₂ (() , _) , _)

    rl-lemma :
      ∀ {Q μ} →
      (! a ∙ ∣ ! b ∙) ∣ ! co a ∙ [ μ ]⟶ Q →
      (! a ∙ ∣ ! b ∙) ∣ ! co a ∙ ∼ Q
        ×
      (μ ≡ name a ⊎ μ ≡ name b ⊎ μ ≡ name (co a) ⊎ μ ≡ τ)
    rl-lemma (par-left (par-left {P′ = P} tr)) =
      case 6-1-3-2 tr of λ where
        (inj₁ (.∅ , action , P∼!a∣∅)) →
            ((! a ∙ ∣ ! b ∙) ∣ ! co a ∙        ∼⟨ (symmetric ∣-right-identity ∣-cong reflexive) ∣-cong reflexive ⟩
             ((! a ∙ ∣ ∅) ∣ ! b ∙) ∣ ! co a ∙  ∼⟨ (symmetric P∼!a∣∅ ∣-cong reflexive) ∣-cong reflexive ⟩■
             (P ∣ ! b ∙) ∣ ! co a ∙)
          , inj₁ refl

        (inj₂ (refl , .∅ , _ , .a , action , a[a̅]⟶ , _)) →
          ⊥-elim (names-are-not-inverted a[a̅]⟶)

    rl-lemma (par-left (par-right {Q′ = P} tr)) =
      case 6-1-3-2 tr of λ where
        (inj₁ (.∅ , action , P∼!b∣∅)) →
            ((! a ∙ ∣ ! b ∙) ∣ ! co a ∙        ∼⟨ (reflexive ∣-cong symmetric ∣-right-identity) ∣-cong reflexive ⟩
             (! a ∙ ∣ (! b ∙ ∣ ∅)) ∣ ! co a ∙  ∼⟨ (reflexive ∣-cong symmetric P∼!b∣∅) ∣-cong reflexive ⟩■
             (! a ∙ ∣ P) ∣ ! co a ∙)
          , inj₂ (inj₁ refl)

        (inj₂ (_ , .∅ , _ , .b , action , b[b̅]⟶ , _)) →
          ⊥-elim (names-are-not-inverted b[b̅]⟶)

    rl-lemma (par-left (par-τ {P′ = P} {Q′ = Q} tr₁ tr₂)) =
      case 6-1-3-2 tr₁ ,′ 6-1-3-2 tr₂ of λ where
        (inj₁ (.∅ , action , P∼!a∣∅) ,
         inj₁ (.∅ , action , Q∼!b∣∅)) →
            ((! a ∙ ∣ ! b ∙) ∣ ! co a ∙              ∼⟨ symmetric (∣-right-identity ∣-cong ∣-right-identity) ∣-cong reflexive ⟩
             ((! a ∙ ∣ ∅) ∣ (! b ∙ ∣ ∅)) ∣ ! co a ∙  ∼⟨ symmetric (P∼!a∣∅ ∣-cong Q∼!b∣∅) ∣-cong reflexive ⟩■
             (P ∣ Q) ∣ ! co a ∙)
          , inj₂ (inj₂ (inj₂ refl))

        (inj₂ (() , _) , _)
        (_ , inj₂ (() , _))

    rl-lemma (par-right {Q′ = Q} tr) =
      case 6-1-3-2 tr of λ where
        (inj₁ (.∅ , action , Q∼!a̅∣∅)) →
            ((! a ∙ ∣ ! b ∙) ∣ ! co a ∙        ∼⟨ reflexive ∣-cong symmetric ∣-right-identity ⟩
             (! a ∙ ∣ ! b ∙) ∣ (! co a ∙ ∣ ∅)  ∼⟨ reflexive ∣-cong symmetric Q∼!a̅∣∅ ⟩■
             (! a ∙ ∣ ! b ∙) ∣ Q)
          , inj₂ (inj₂ (inj₁ refl))

        (inj₂ (_ , .∅ , _ , .(co a) , action , a̅[a̅̅]⟶ , _)) →
          ⊥-elim (names-are-not-inverted a̅[a̅̅]⟶)

    rl-lemma (par-τ {Q′ = Q} (par-left {P′ = P} tr₁) tr₂) =
      case 6-1-3-2 tr₁ ,′ 6-1-3-2 tr₂ of λ where
        (inj₁ (.∅ , action , P∼!a∣∅) ,
         inj₁ (R  , tr     , Q∼!a̅∣R)) →
            ((! a ∙ ∣ ! b ∙) ∣ ! co a ∙              ∼⟨ symmetric ((∣-right-identity ∣-cong reflexive) ∣-cong ∣-right-identity) ⟩
             ((! a ∙ ∣ ∅) ∣ ! b ∙) ∣ (! co a ∙ ∣ ∅)  ∼≡⟨ cong (λ R → _ ∣ (_ ∣ R)) (sym $ ·-only⟶ tr) ⟩
             ((! a ∙ ∣ ∅) ∣ ! b ∙) ∣ (! co a ∙ ∣ R)  ∼⟨ symmetric ((P∼!a∣∅ ∣-cong reflexive) ∣-cong Q∼!a̅∣R) ⟩■
             (P ∣ ! b ∙) ∣ Q)
          , inj₂ (inj₂ (inj₂ refl))

        (inj₂ (() , _) , _)
        (_ , inj₂ (() , _))

    rl-lemma (par-τ {Q′ = Q} (par-right {Q′ = P} tr₁) tr₂) =
      case 6-1-3-2 tr₁ ,′ 6-1-3-2 tr₂ of λ where
        (inj₁ (.∅ , action , P∼!b∣∅) ,
         inj₁ (R  , tr     , Q∼!a̅∣R)) →
            ((! a ∙ ∣ ! b ∙) ∣ ! co a ∙              ∼⟨ symmetric ((reflexive ∣-cong ∣-right-identity) ∣-cong ∣-right-identity) ⟩
             (! a ∙ ∣ (! b ∙ ∣ ∅)) ∣ (! co a ∙ ∣ ∅)  ∼≡⟨ cong (λ R → _ ∣ (_ ∣ R)) (sym $ ·-only⟶ tr) ⟩
             (! a ∙ ∣ (! b ∙ ∣ ∅)) ∣ (! co a ∙ ∣ R)  ∼⟨ symmetric ((reflexive ∣-cong P∼!b∣∅) ∣-cong Q∼!a̅∣R) ⟩■
             (! a ∙ ∣ P) ∣ Q)
          , inj₂ (inj₂ (inj₂ refl))

        (inj₂ (() , _) , _)
        (_ , inj₂ (() , _))

    rl :
      ∀ {Q μ} →
      (! a ∙ ∣ ! b ∙) ∣ ! co a ∙ [ μ ]⟶ Q →
      ∃ λ P → ! name a ∙ (b ∙) ∣ ! co a ∙ [ μ ]⇒̂ P × [ i ] P ≈′ Q
    rl {Q} tr = case rl-lemma tr of λ where
      (!a∣!b∣!a̅∼Q , inj₁ refl) →
        ! name a ∙ (b ∙) ∣ ! co a ∙          →⟨ ⟶: par-left (replication (par-right action)) ⟩■
          W.⇒̂[ name a ]
        (! name a ∙ (b ∙) ∣ b ∙) ∣ ! co a ∙  ∼⟨ swap-rightmost ⟩
        (! name a ∙ (b ∙) ∣ ! co a ∙) ∣ b ∙  ∼′⟨ 6-5-4′ WL.∣-cong′ reflexive ⟩
        ((! a ∙ ∣ ! b ∙) ∣ ! co a ∙) ∣ b ∙   ∼⟨ swap-rightmost ⟩
        ((! a ∙ ∣ ! b ∙) ∣ b ∙) ∣ ! co a ∙   ∼⟨ symmetric ∣-assoc ∣-cong reflexive ⟩
        (! a ∙ ∣ (! b ∙ ∣ b ∙)) ∣ ! co a ∙   ∼⟨ (reflexive ∣-cong 6-1-2) ∣-cong reflexive ⟩ ∼:
        (! a ∙ ∣ ! b ∙) ∣ ! co a ∙           ∼⟨ !a∣!b∣!a̅∼Q ⟩■
        Q

      (!a∣!b∣!a̅∼Q , inj₂ (inj₁ refl)) →
        ! name a ∙ (b ∙) ∣ ! co a ∙                  →⟨ par-τ (replication (par-right action))
                                                              (replication (par-right action)) ⟩
        (! name a ∙ (b ∙) ∣ (b ∙)) ∣ (! co a ∙ ∣ ∅)  →⟨ ⟶: par-left (par-right action) ⟩■
          W.⇒̂[ name b ]
        (! name a ∙ (b ∙) ∣ ∅) ∣ (! co a ∙ ∣ ∅)      ∼⟨ ∣-right-identity ∣-cong ∣-right-identity ⟩
        (! name a ∙ (b ∙)) ∣ ! co a ∙                ∼′⟨ 6-5-4′ ⟩ ∼:
        (! a ∙ ∣ ! b ∙) ∣ ! co a ∙                   ∼⟨ !a∣!b∣!a̅∼Q ⟩■
        Q

      (!a∣!b∣!a̅∼Q , inj₂ (inj₂ (inj₁ refl))) →
        ! name a ∙ (b ∙) ∣ ! co a ∙        →⟨ ⟶: par-right (replication (par-right action)) ⟩■
          W.⇒̂[ name (co a) ]
        ! name a ∙ (b ∙) ∣ (! co a ∙ ∣ ∅)  ∼⟨ reflexive ∣-cong ∣-right-identity ⟩
        ! name a ∙ (b ∙) ∣ ! co a ∙        ∼′⟨ 6-5-4′ ⟩ ∼:
        (! a ∙ ∣ ! b ∙) ∣ ! co a ∙         ∼⟨ !a∣!b∣!a̅∼Q ⟩■
        Q

      (!a∣!b∣!a̅∼Q , inj₂ (inj₂ (inj₂ refl))) →
        ! name a ∙ (b ∙) ∣ ! co a ∙  ■
          W.⇒̂[ τ ]
        ! name a ∙ (b ∙) ∣ ! co a ∙  ∼′⟨ 6-5-4′ ⟩ ∼:
        (! a ∙ ∣ ! b ∙) ∣ ! co a ∙   ∼⟨ !a∣!b∣!a̅∼Q ⟩■
        Q

  6-5-4′ :
    ∀ {i a b} →
    [ i ] ! name a ∙ (b ∙) ∣ ! co a ∙ ≈′ (! a ∙ ∣ ! b ∙) ∣ ! co a ∙
  force 6-5-4′ = 6-5-4

-- The first part of Exercise 6.5.8.

6-5-8-1 :
  ∀ a {P Q} →
  ⟨ν proj₁ a ⟩ (name a ∙ P ∣ name (co a) ∙ Q) ≳ ⟨ν proj₁ a ⟩ (P ∣ Q)
6-5-8-1 a {P} {Q} = E.⟨ lr , rl ⟩
  where
  lr :
    ∀ {μ R} →
    ⟨ν proj₁ a ⟩ (name a ∙ P ∣ name (co a) ∙ Q) [ μ ]⟶ R →
    ∃ λ R′ → ⟨ν proj₁ a ⟩ (P ∣ Q) [ μ ]⟶̂ R′ × R ≳′ R′
  lr (restriction a∉μ (par-left action))          = ⊥-elim (a∉μ refl)
  lr (restriction a∉μ (par-right action))         = ⊥-elim (a∉μ refl)
  lr (restriction a∉μ (par-τ {Q′ = R} action tr)) =
    ⟨ν proj₁ a ⟩ (P ∣ R)  ∼≡⟨ cong (λ R → ⟨ν _ ⟩ (_ ∣ R)) (·-only⟶ tr) ⟩■
    ⟨ν proj₁ a ⟩ (P ∣ Q)
      ⟵̂[ τ ]
    ⟨ν proj₁ a ⟩ (P ∣ Q)  ■

  rl :
    ∀ {μ R′} →
    ⟨ν proj₁ a ⟩ (P ∣ Q) [ μ ]⟶ R′ →
    ∃ λ R → ⟨ν proj₁ a ⟩ (name a ∙ P ∣ name (co a) ∙ Q) [ μ ]⇒ R ×
            R ≳′ R′
  rl {μ} (restriction {P′ = R} a∉μ P∣Q⟶R) =
    ⟨ν proj₁ a ⟩ (name a ∙ P ∣ name (co a) ∙ Q)  →⟨ ⟶: restriction _ (par-τ action action) ⟩
    ⟨ν proj₁ a ⟩ (P ∣ Q)                         →⟨ ⟶: restriction a∉μ P∣Q⟶R ⟩■
      E.⇒[ μ ]
    ⟨ν proj₁ a ⟩ R                               ■

-- One interpretation of the second part of Exercise 6.5.8 is
-- contradictory, assuming that Name is inhabited.

¬-6-5-8-2 :
  Name →
  ¬ (∀ {a b P} →
     ! ⟨ν proj₁ a ⟩ (name b ∙ (a ∙) ∣ name (co a) ∙ P) ≈
     ! name b ∙ ⟨ν proj₁ a ⟩ P)
¬-6-5-8-2 x =
  (∀ {a b P} →
   ! ⟨ν proj₁ a ⟩ (name b ∙ (a ∙) ∣ name (co a) ∙ P) ≈
   ! name b ∙ ⟨ν proj₁ a ⟩ P)                                          ↝⟨ (λ hyp → hyp {a = a} {b = co a}) ⟩

  (! ⟨ν proj₁ a ⟩ (name (co a) ∙ (a ∙) ∣ co a ∙) ≈
   ! name (co a) ∙ ⟨ν proj₁ a ⟩ ∅)                                     ↝⟨ (λ hyp → Σ-map id proj₁ $ W.right-to-left hyp
                                                                                                      (replication (par-right action))) ⟩
  ∃ (! ⟨ν proj₁ a ⟩ (name (co a) ∙ (a ∙) ∣ co a ∙) [ name (co a) ]⇒̂_)  ↝⟨ !P⇒̂ ∘ proj₂ ⟩□

  ⊥                                                                    □
  where
  a = x , true

  P = ⟨ν proj₁ a ⟩ (name (co a) ∙ (a ∙) ∣ co a ∙)

  P⟶ : ∀ {μ Q} → ¬ P [ μ ]⟶ Q
  P⟶ (restriction x≢x (par-left action))  = ⊥-elim (x≢x refl)
  P⟶ (restriction x≢x (par-right action)) = ⊥-elim (x≢x refl)
  P⟶ (restriction _   (par-τ action tr))  = names-are-not-inverted tr

  !P⟶ : ∀ {μ Q} → ¬ ! P [ μ ]⟶ Q
  !P⟶ (replication (par-left tr))  = !P⟶ tr
  !P⟶ (replication (par-right tr)) = P⟶ tr
  !P⟶ (replication (par-τ _ tr))   = P⟶ tr

  !P⇒ : ∀ {Q} → ! P ⇒ Q → Q ≡ ! P
  !P⇒ done          = refl
  !P⇒ (step _ tr _) = ⊥-elim (!P⟶ tr)

  !P[]⇒ : ∀ {μ Q} → ¬ ! P [ μ ]⇒ Q
  !P[]⇒ (steps trs tr _) rewrite !P⇒ trs = !P⟶ tr

  !P⇒̂ : ∀ {b Q} → ¬ ! P [ name b ]⇒̂ Q
  !P⇒̂ (silent () _)
  !P⇒̂ (non-silent _ tr) = !P[]⇒ tr

-- Another interpretation of the second part of Exercise 6.5.8 can be
-- proved.

6-5-8-2 :
  ∀ {i a b P} →
  proj₁ a ≢ proj₁ b →
  [ i ] ! ⟨ν proj₁ a ⟩ (name b ∙ (a ∙) ∣ name (co a) ∙ P) ≈
        ! name b ∙ ⟨ν proj₁ a ⟩ P
6-5-8-2 {i} {a} {b} {P} a≢b = W.⟨ lr , rl ⟩
  where
  6-5-8-2′ :
    [ i ] ! ⟨ν proj₁ a ⟩ (name b ∙ (a ∙) ∣ name (co a) ∙ P) ≈′
          ! name b ∙ ⟨ν proj₁ a ⟩ P
  force 6-5-8-2′ = 6-5-8-2 a≢b

  lr :
    ∀ {Q μ} →
    ! ⟨ν proj₁ a ⟩ (name b ∙ (a ∙) ∣ name (co a) ∙ P) [ μ ]⟶ Q →
    ∃ λ Q′ → ! name b ∙ ⟨ν proj₁ a ⟩ P [ μ ]⇒̂ Q′ × [ i ] Q ≈′ Q′
  lr {Q} tr = case 6-1-3-2 tr of λ where
    (inj₁ (_ , restriction a≢b (par-left action)
             , Q∼!νa[ba∣a̅P]∣νa[a∣a̅P])) →
      Q                                                    ∼⟨ Q∼!νa[ba∣a̅P]∣νa[a∣a̅P] ⟩

      ! ⟨ν proj₁ a ⟩ (name b ∙ (a ∙) ∣ name (co a) ∙ P) ∣
      ⟨ν proj₁ a ⟩ (a ∙ ∣ name (co a) ∙ P)                 ∼⟨ (_ ■) EL.∣-cong 6-5-8-1 _ ⟩ ≈′:

      ! ⟨ν proj₁ a ⟩ (name b ∙ (a ∙) ∣ name (co a) ∙ P) ∣
      ⟨ν proj₁ a ⟩ (∅ ∣ P)                                 ∼⟨ 6-5-8-2′ WL.∣-cong′ convert {a = ℓ} (⟨ν refl ⟩-cong ∣-left-identity) ⟩■

      ! name b ∙ ⟨ν proj₁ a ⟩ P ∣ ⟨ν proj₁ a ⟩ P

        W.⇐̂[ name b ]                                      ←⟨ ⟶: replication (par-right action) ⟩■

      ! name b ∙ ⟨ν proj₁ a ⟩ P

    (inj₁ (_ , restriction _ (par-τ action tr) , _)) →
      ⊥-elim (                              $⟨ tr ⟩
        name (co a) · _ [ name (co b) ]⟶ _  ↝⟨ ·-only ⟩
        name (co a) ≡ name (co b)           ↝⟨ cancel-name ⟩
        co a ≡ co b                         ↝⟨ cong proj₁ ⟩
        proj₁ a ≡ proj₁ b                   ↝⟨ a≢b ⟩□
        ⊥                                   □)

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
      name (co a) ∙ P [ name (co b) ]⟶ _  ↝⟨ cong proj₁ ∘ cancel-name ∘ ·-only ⟩
      proj₁ a ≡ proj₁ b                   ↝⟨ a≢b ⟩
      ⊥                                   ↝⟨ ⊥-elim ⟩□
      _                                   □

    (inj₂ (refl , _ , _ , c
                , restriction a≢c (par-right tr)
                , restriction _   (par-left action)
                , _)) →
                                     $⟨ tr ⟩
      name (co a) ∙ P [ name c ]⟶ _  ↝⟨ cong proj₁ ∘ cancel-name ∘ ·-only ⟩
      proj₁ a ≡ proj₁ c              ↝⟨ a≢c ⟩
      ⊥                              ↝⟨ ⊥-elim ⟩□
      _                              □

  rl :
    ∀ {Q′ μ} →
    ! name b ∙ ⟨ν proj₁ a ⟩ P [ μ ]⟶ Q′ →
    ∃ λ Q → ! ⟨ν proj₁ a ⟩ (name b ∙ (a ∙) ∣ name (co a) ∙ P) [ μ ]⇒̂ Q ×
            [ i ] Q ≈′ Q′
  rl {Q′} tr = case 6-1-3-2 tr of λ where
    (inj₁ (_ , action , Q′∼!bνaP∣νaP)) →
      ! ⟨ν proj₁ a ⟩ (name b ∙ (a ∙) ∣ name (co a) ∙ P)    →⟨ ⟶: replication (par-right (restriction a≢b (par-left action))) ⟩■

        W.⇒̂[ name b ]

      ! ⟨ν proj₁ a ⟩ (name b ∙ (a ∙) ∣ name (co a) ∙ P) ∣
      ⟨ν proj₁ a ⟩ (a ∙ ∣ name (co a) ∙ P)                 ∼′⟨ 6-5-8-2′ WL.∣-cong′ convert {a = ℓ} (6-5-8-1 a) ⟩

      ! name b ∙ ⟨ν proj₁ a ⟩ P ∣ ⟨ν proj₁ a ⟩ (∅ ∣ P)     ∼⟨ (_ ■) ∣-cong ⟨ν refl ⟩-cong ∣-left-identity ⟩ ∼:

      ! name b ∙ ⟨ν proj₁ a ⟩ P ∣ ⟨ν proj₁ a ⟩ P           ∼⟨ symmetric Q′∼!bνaP∣νaP ⟩■

      Q′

    (inj₂ (refl , _ , _ , _ , action , tr , _)) →
      ⊥-elim (names-are-not-inverted tr)
