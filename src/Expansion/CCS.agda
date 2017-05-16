------------------------------------------------------------------------
-- Lemmas related to expansion and CCS
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Expansion.CCS {Name : Set} where

open import Equality.Propositional
open import Prelude hiding (module W)

open import Function-universe equality-with-J hiding (_∘_)

open import Labelled-transition-system

open CCS Name
open LTS CCS hiding (Proc; _[_]⟶_)

import Bisimilarity.Coinductive CCS as S
import Bisimilarity.Coinductive.Equational-reasoning-instances
open import Bisimilarity.Coinductive CCS using (_∼_)
import Bisimilarity.Exercises.Coinductive as S
open import Bisimilarity.Weak.Coinductive.Other CCS as W
  using (_≈_; force)
import
  Bisimilarity.Weak.Coinductive.Other.Equational-reasoning-instances
open import Equational-reasoning
open import Expansion CCS
import Expansion.Equational-reasoning-instances
import Labelled-transition-system.Equational-reasoning-instances CCS
  as Unused
open import Relation

-- Some lemmas used to prove the congruence lemmas below as well as
-- similar results in Bisimilarity.Weak.CCS.

module Cong-lemmas
  ({R} R′ : Proc → Proc → Set)
  ⦃ _ : Reflexive R ⦄
  ⦃ _ : Reflexive R′ ⦄
  ⦃ _ : Convertible R R ⦄
  ⦃ _ : Convertible R R′ ⦄
  ⦃ _ : Convertible R′ R′ ⦄
  ⦃ _ : Transitive′ R _∼_ ⦄
  ⦃ _ : Transitive′ R′ _∼_ ⦄
  ⦃ _ : Transitive _∼_ R′ ⦄
  (right-to-left :
   ∀ {P Q} → R P Q →
   ∀ {Q′ μ} → Q [ μ ]⟶ Q′ → ∃ λ P′ → P [ μ ]⇒̂ P′ × R′ P′ Q′)
  where

  private

    infix -3 rl-result-⇒̂′

    rl-result-⇒̂′ : ∀ {P P′ Q′} μ → P [ μ ]⇒̂ P′ → R′ P′ Q′ →
                   ∃ λ P′ → P [ μ ]⇒̂ P′ × R′ P′ Q′
    rl-result-⇒̂′ _ P⇒̂P′ P′≳′Q′ = _ , P⇒̂P′ , P′≳′Q′

    syntax rl-result-⇒̂′ μ P⇒̂P′ P′≳′Q′ = P⇒̂P′ ⇒̂[ μ ]′ P′≳′Q′

  ∣-cong :
    (∀ {P P′ Q Q′} → R′ P P′ → R′ Q Q′ → R′ (P ∣ Q) (P′ ∣ Q′)) →
    ∀ {P₁ P₂ Q₁ Q₂ R₂ μ} →
    R P₁ P₂ → R Q₁ Q₂ → P₂ ∣ Q₂ [ μ ]⟶ R₂ →
    ∃ λ R₁ → P₁ ∣ Q₁ [ μ ]⇒̂ R₁ × R′ R₁ R₂
  ∣-cong _∣-cong′_ P₁≳P₂ Q₁≳Q₂ = λ where
    (par-left  tr)  → Σ-map (_∣ _)
                        (Σ-map (map-⇒̂ par-left)
                               (_∣-cong′ convert Q₁≳Q₂))
                        (right-to-left P₁≳P₂ tr)
    (par-right tr)  → Σ-map (_ ∣_)
                        (Σ-map (map-⇒̂ par-right)
                               (convert P₁≳P₂ ∣-cong′_))
                        (right-to-left Q₁≳Q₂ tr)
    (par-τ tr₁ tr₂) → Σ-zip _∣_
                        (Σ-zip (zip-⇒̂ par-left par-right
                                      (λ ()) (λ _ ()) (λ ())
                                      par-τ)
                               _∣-cong′_)
                        (right-to-left P₁≳P₂ tr₁)
                        (right-to-left Q₁≳Q₂ tr₂)

  ·-cong :
    ∀ {P₁ P₂ Q₂ μ μ′} →
    R P₁ P₂ → μ · P₂ [ μ′ ]⟶ Q₂ →
    ∃ λ Q₁ → μ · P₁ [ μ′ ]⇒̂ Q₁ × R′ Q₁ Q₂
  ·-cong P₁≳P₂ action = _ , ⟶→⇒̂ action , convert P₁≳P₂

  ν-cong :
    (∀ {a P P′} → R′ P P′ → R′ (ν a P) (ν a P′)) →
    ∀ {a μ P P′ Q′} →
    R P P′ → ν a P′ [ μ ]⟶ Q′ →
    ∃ λ Q → ν a P [ μ ]⇒̂ Q × R′ Q Q′
  ν-cong ν-cong′ {a} {μ} {P} P≳P′ (restriction {P′ = Q′} a∉μ P′⟶Q′) =
    case right-to-left P≳P′ P′⟶Q′ of λ where
      (Q , P⇒̂Q , Q≳′Q′) →
        ν a P      →⟨ map-⇒̂′ (λ { refl → restriction _ }) (restriction a∉μ) P⇒̂Q ⟩■
          ⇒̂[ μ ]′
        ν a Q      ∼⟨ ν-cong′ Q≳′Q′ ⟩■
        ν a Q′

  !-cong-lemma₁ : ∀ {P Q μ} → P [ μ ]⇒ Q → ! P [ μ ]⇒ ! P ∣ Q
  !-cong-lemma₁ {P} {Q} {μ} = λ where
    (steps {q′ = Q′} done P⟶Q′ Q′⇒Q) →
      ! P       [ μ ]⇒⟨ replication (par-right P⟶Q′) ⟩
      ! P ∣ Q′  →⟨ map-⇒ par-right Q′⇒Q ⟩■
      ! P ∣ Q

    (steps {p′ = P″} {q′ = Q′}
           (step {q = P′} {μ = μ′} μ′s P⟶P′ P′⇒P″)
           P″⟶Q′ Q′⇒Q) →
      ! P       →⟨ ⟶→⇒ μ′s (replication (par-right P⟶P′)) ⟩
      ! P ∣ P′  →⟨ map-⇒ par-right P′⇒P″ ⟩
      ! P ∣ P″  [ μ ]⇒⟨ par-right P″⟶Q′ ⟩
      ! P ∣ Q′  →⟨ map-⇒ par-right Q′⇒Q ⟩■
      ! P ∣ Q

  !-cong-lemma₂ :
    ∀ {P Q₁ Q₂ a} →
    P [ name a ]⇒ Q₁ → P [ name (co a) ]⇒ Q₂ →
    ∃ λ R → ! P [ τ ]⇒ R × R ∼ (! P ∣ Q₁) ∣ Q₂
  !-cong-lemma₂ {P} {Q₁} {Q₂} {a} = λ where
    (steps {q′ = Q₁′} done P⟶Q₁′ Q₁′⇒Q₁)
      (steps {q′ = Q₂′} done P⟶Q₂′ Q₂′⇒Q₂) →
        _
      , (! P                [ τ ]⇒⟨ replication (par-τ (replication (par-right P⟶Q₁′)) P⟶Q₂′) ⟩
         (! P ∣ Q₁′) ∣ Q₂′  →⟨ zip-⇒ par-left par-right (map-⇒ par-right Q₁′⇒Q₁) Q₂′⇒Q₂ ⟩■
         (! P ∣ Q₁) ∣ Q₂)
      , reflexive

    (steps {q′ = Q₁′} done P⟶Q₁′ Q₁′⇒Q₁)
      (steps {p′ = P₂″} {q′ = Q₂′}
             (step {q = P₂′} {μ = μ} μs P⟶P₂′ P₂′⇒P₂″)
             P₂″⟶Q₂′ Q₂′⇒Q₂) →
        _
      , (! P                →⟨ ⟶→⇒ μs (replication (par-right P⟶P₂′)) ⟩
         ! P ∣ P₂′          →⟨ map-⇒ par-right P₂′⇒P₂″ ⟩
         ! P ∣ P₂″          [ τ ]⇒⟨ par-τ (replication (par-right P⟶Q₁′)) P₂″⟶Q₂′ ⟩
         (! P ∣ Q₁′) ∣ Q₂′  →⟨ zip-⇒ par-left par-right (map-⇒ par-right Q₁′⇒Q₁) Q₂′⇒Q₂ ⟩■
         (! P ∣ Q₁) ∣ Q₂)
      , reflexive

    (steps {p′ = P₁″} {q′ = Q₁′}
           (step {q = P₁′} {μ = μ} μs P⟶P₁′ P₁′⇒P₁″)
           P₁″⟶Q₁′ Q₁′⇒Q₁)
      (steps {q′ = Q₂′} done P⟶Q₂′ Q₂′⇒Q₂) →
        _
      , (! P                →⟨ ⟶→⇒ μs (replication (par-right P⟶P₁′)) ⟩
         ! P ∣ P₁′          →⟨ map-⇒ par-right P₁′⇒P₁″ ⟩
         ! P ∣ P₁″          [ τ ]⇒⟨ par-τ′ (sym $ co-involutive a) (replication (par-right P⟶Q₂′)) P₁″⟶Q₁′ ⟩
         (! P ∣ Q₂′) ∣ Q₁′  →⟨ zip-⇒ par-left par-right (map-⇒ par-right Q₂′⇒Q₂) Q₁′⇒Q₁ ⟩■
         (! P ∣ Q₂) ∣ Q₁)
      , ((! P ∣ Q₂) ∣ Q₁  ∼⟨ S.swap-rightmost ⟩■
         (! P ∣ Q₁) ∣ Q₂)

    (steps {p′ = P₁″} {q′ = Q₁′}
           (step {q = P₁′} {μ = μ₁} μ₁s P⟶P₁′ P₁′⇒P₁″)
           P₁″⟶Q₁′ Q₁′⇒Q₁)
      (steps {p′ = P₂″} {q′ = Q₂′}
             (step {q = P₂′} {μ = μ₂} μ₂s P⟶P₂′ P₂′⇒P₂″)
             P₂″⟶Q₂′ Q₂′⇒Q₂) →
        _
      , (! P                →⟨ ⟶→⇒ μ₂s (replication (par-right P⟶P₂′)) ⟩
         ! P ∣ P₂′          →⟨ ⟶→⇒ μ₁s (par-left (replication (par-right P⟶P₁′))) ⟩
         (! P ∣ P₁′) ∣ P₂′  →⟨ zip-⇒ par-left par-right (map-⇒ par-right P₁′⇒P₁″) P₂′⇒P₂″ ⟩
         (! P ∣ P₁″) ∣ P₂″  [ τ ]⇒⟨ par-τ (par-right P₁″⟶Q₁′) P₂″⟶Q₂′ ⟩
         (! P ∣ Q₁′) ∣ Q₂′  →⟨ zip-⇒ par-left par-right (map-⇒ par-right Q₁′⇒Q₁) Q₂′⇒Q₂ ⟩■
         (! P ∣ Q₁) ∣ Q₂)
      , reflexive

  !-cong :
    (∀ {P P′ Q Q′} → R′ P P′ → R′ Q Q′ → R′ (P ∣ Q) (P′ ∣ Q′)) →
    (∀ {P P′} → R′ P P′ → R′ (! P) (! P′)) →
    ∀ {P P′ Q′ μ} →
    R P P′ → ! P′ [ μ ]⟶ Q′ →
    ∃ λ Q → ! P [ μ ]⇒̂ Q × R′ Q Q′
  !-cong _∣-cong′_ !-cong′_ {P} {P′} {Q′} {μ} P≳P′ !P′⟶Q′ =
    case S.6-1-3-2 !P′⟶Q′ of λ where

      (inj₁ (P″ , P′⟶P″ , Q′∼!P′∣P″)) →
        case right-to-left P≳P′ P′⟶P″ of λ where
          (_ , silent μs done , P≳′P″) →
            ! P        →⟨ silent μs done ⟩■
              ⇒̂[ μ ]′
            ! P        ∼⟨ symmetric S.6-1-2 ⟩
            ! P ∣ P    ∼′⟨ (!-cong′ (convert P≳P′)) ∣-cong′ P≳′P″ ⟩ S.∼:
            ! P′ ∣ P″  ∼⟨ symmetric Q′∼!P′∣P″ ⟩■
            Q′

          (Q , silent μs (step {q = R} {μ = μ′} μ′s P⟶R R⇒Q) , Q≳′P″) →
            ! P        →⟨ ⟶→⇒ μ′s (replication (par-right P⟶R)) ⟩
            ! P ∣ R    →⟨ silent μs (map-⇒ par-right R⇒Q) ⟩■
              ⇒̂[ μ ]′
            ! P ∣ Q    ∼′⟨ (!-cong′ (convert P≳P′)) ∣-cong′ Q≳′P″ ⟩ S.∼:
            ! P′ ∣ P″  ∼⟨ symmetric Q′∼!P′∣P″ ⟩■
            Q′

          (Q , non-silent ¬μs P⇒Q , Q≳′P″) →
            ! P        →⟨ non-silent ¬μs (!-cong-lemma₁ P⇒Q) ⟩■
              ⇒̂[ μ ]′
            ! P ∣ Q    ∼′⟨ (!-cong′ (convert P≳P′)) ∣-cong′ Q≳′P″ ⟩ S.∼:
            ! P′ ∣ P″  ∼⟨ symmetric Q′∼!P′∣P″ ⟩■
            Q′

      (inj₂ (refl , P″ , P‴ , a , P′⟶P″ , P′⟶P‴ , Q′∼!P′∣P″∣P‴)) →
        case right-to-left P≳P′ P′⟶P″ ,′
             right-to-left P≳P′ P′⟶P‴ of λ where
          ((_ , silent () _ , _) , _)
          (_ , (_ , silent () _ , _))

          ((Q₁ , non-silent _ P⇒Q₁ , Q₁≳′P″) ,
           (Q₂ , non-silent _ P⇒Q₂ , Q₂≳′P‴)) →
            case !-cong-lemma₂ P⇒Q₁ P⇒Q₂ of λ where
              (R , !P⇒R , R∼[!P∣Q₁]∣Q₂) →
                ! P               →⟨ !P⇒R ⟩■
                  ⇒̂[ τ ]′
                R                 ∼⟨ R∼[!P∣Q₁]∣Q₂ ⟩
                (! P ∣ Q₁) ∣ Q₂   ∼′⟨ ((!-cong′ (convert P≳P′)) ∣-cong′ Q₁≳′P″) ∣-cong′ Q₂≳′P‴ ⟩ S.∼:
                (! P′ ∣ P″) ∣ P‴  ∼⟨ symmetric Q′∼!P′∣P″∣P‴ ⟩■
                Q′

  ⊕·-cong :
    ∀ {P Q Q′ S′ μ μ′} →
    R Q Q′ → P ⊕ μ · Q′ [ μ′ ]⟶ S′ →
    ∃ λ S → P ⊕ μ · Q [ μ′ ]⇒̂ S × R′ S S′
  ⊕·-cong {P} {Q} {Q′} {S′} {μ} {μ′} Q≳Q′ = λ where
    (choice-left P⟶S′) →
      P ⊕ μ · Q  →⟨ choice-left P⟶S′ ⟩■
        ⇒̂[ μ′ ]′
      S′         ■

    (choice-right action) →
      P ⊕ μ · Q  →⟨ choice-right action ⟩■
        ⇒̂[ μ ]′
      Q          ∼⟨ Q≳Q′ ⟩■
      Q′

  ·⊕·-cong :
    ∀ {μ₁ μ₂ P₁ P₁′ P₂ P₂′ S′ μ} →
    R P₁ P₁′ → R P₂ P₂′ → μ₁ · P₁′ ⊕ μ₂ · P₂′ [ μ ]⟶ S′ →
    ∃ λ S → μ₁ · P₁ ⊕ μ₂ · P₂ [ μ ]⇒̂ S × R′ S S′
  ·⊕·-cong {μ₁} {μ₂} {P₁} {P₁′} {P₂} {P₂′} P₁≳P₁′ P₂≳P₂′ = λ where
    (choice-left action) →
      μ₁ · P₁ ⊕ μ₂ · P₂  →⟨ choice-left action ⟩■
        ⇒̂[ μ₁ ]′
      P₁                 ∼⟨ P₁≳P₁′ ⟩■
      P₁′

    (choice-right action) →
      μ₁ · P₁ ⊕ μ₂ · P₂  →⟨ choice-right action ⟩■
        ⇒̂[ μ₂ ]′
      P₂                 ∼⟨ P₂≳P₂′ ⟩■
      P₂′

  []-cong :
    (∀ {P P′ Q Q′} → R P P′ → R Q Q′ → R (P ∣ Q) (P′ ∣ Q′)) →
    (∀ {μ μ′ P P′} → μ ≡ μ′ → R P P′ → R (μ · P) (μ′ · P′)) →
    (∀ {a a′ P P′} → a ≡ a′ → R P P′ → R (ν a P) (ν a′ P′)) →
    (∀ {P P′} → R P P′ → R (! P) (! P′)) →
    (∀ {P μ Q Q′} → R Q Q′ → R (P ⊕ μ · Q) (P ⊕ μ · Q′)) →
    (∀ {P P′ μ Q} → R P P′ → R (μ · P ⊕ Q) (μ · P′ ⊕ Q)) →
    (∀ {μ₁ μ₂ P₁ P₁′ P₂ P₂′} → R P₁ P₁′ → R P₂ P₂′ →
     R (μ₁ · P₁ ⊕ μ₂ · P₂) (μ₁ · P₁′ ⊕ μ₂ · P₂′)) →
    ∀ {n Ps Qs} {C : Context n} →
    (∀ x → R (Ps x) (Qs x)) → Non-degenerate C →
    R (C [ Ps ]) (C [ Qs ])
  []-cong ∣-cong ·-cong ν-cong !-cong ⊕·-cong ·⊕-cong ·⊕·-cong
          {n} {Ps} {Qs} Ps≳Qs = []-cong′
    where
    mutual

      []-cong′ : ∀ {C} → Non-degenerate C → R (C [ Ps ]) (C [ Qs ])
      []-cong′ = λ where
        hole       → Ps≳Qs _
        ∅          → reflexive
        (D₁ ∣ D₂)  → ∣-cong ([]-cong′ D₁) ([]-cong′ D₂)
        (D₁ ⊕ D₂)  → ⊕-cong D₁ D₂
        (action D) → ·-cong refl ([]-cong′ D)
        (ν D)      → ν-cong refl ([]-cong′ D)
        (! D)      → !-cong ([]-cong′ D)

      ⊕-cong :
        {C₁ C₂ : Context n} →
        Non-degenerate-summand C₁ →
        Non-degenerate-summand C₂ →
        R ((C₁ [ Ps ]) ⊕ (C₂ [ Ps ])) ((C₁ [ Qs ]) ⊕ (C₂ [ Qs ]))
      ⊕-cong = λ where
        (process P₁) (process P₂) →
          (context P₁ [ Ps ]) ⊕ (context P₂ [ Ps ])  ∼≡⟨ cong₂ _⊕_ (context-[] P₁) (context-[] P₂) ⟩
          P₁ ⊕ P₂                                    ∼≡⟨ sym $ cong₂ _⊕_ (context-[] P₁) (context-[] P₂) ⟩
          (context P₁ [ Qs ]) ⊕ (context P₂ [ Qs ])  ■

        (process P₁) (action {μ = μ₂} {C = C₂} D₂) →
          (context P₁ [ Ps ]) ⊕ (μ₂ · C₂ [ Ps ])  ∼≡⟨ cong (_⊕ _) (context-[] P₁) ⟩
          P₁ ⊕ (μ₂ · C₂ [ Ps ])                   ∼′⟨ ⊕·-cong ([]-cong′ D₂) ⟩ S.∼:
          P₁ ⊕ (μ₂ · C₂ [ Qs ])                   ∼≡⟨ sym $ cong (_⊕ _) (context-[] P₁) ⟩
          (context P₁ [ Qs ]) ⊕ (μ₂ · C₂ [ Qs ])  ■

        (action {μ = μ₁} {C = C₁} D₁) (process P₂) →
          (μ₁ · C₁ [ Ps ]) ⊕ (context P₂ [ Ps ])  ∼≡⟨ cong (_ ⊕_) (context-[] P₂) ⟩
          (μ₁ · C₁ [ Ps ]) ⊕ P₂                   ∼′⟨ ·⊕-cong ([]-cong′ D₁) ⟩ S.∼:
          (μ₁ · C₁ [ Qs ]) ⊕ P₂                   ∼≡⟨ sym $ cong (_ ⊕_) (context-[] P₂) ⟩
          (μ₁ · C₁ [ Qs ]) ⊕ (context P₂ [ Qs ])  ■

        (action {μ = μ₁} {C = C₁} D₁) (action {μ = μ₂} {C = C₂} D₂) →
          (μ₁ · C₁ [ Ps ]) ⊕ (μ₂ · C₂ [ Ps ])  ∼⟨ ·⊕·-cong ([]-cong′ D₁) ([]-cong′ D₂) ⟩■
          (μ₁ · C₁ [ Qs ]) ⊕ (μ₂ · C₂ [ Qs ])

private
  module CL {i} = Cong-lemmas [ i ]_≳′_ right-to-left

mutual

  -- _∣_ preserves the expansion relation.

  infix 6 _∣-cong_ _∣-cong′_

  _∣-cong_ : ∀ {i P P′ Q Q′} →
             [ i ] P ≳ P′ → [ i ] Q ≳ Q′ → [ i ] P ∣ Q ≳ P′ ∣ Q′
  _∣-cong_ {i} P≳P′ Q≳Q′ =
    ⟨ lr P≳P′ Q≳Q′
    , CL.∣-cong _∣-cong′_ P≳P′ Q≳Q′
    ⟩
    where
    lr : ∀ {P P′ Q Q′ R μ} →
         [ i ] P ≳ P′ → [ i ] Q ≳ Q′ → P ∣ Q [ μ ]⟶ R →
         ∃ λ R′ → P′ ∣ Q′ [ μ ]⟶̂ R′ × [ i ] R ≳′ R′
    lr P≳P′ Q≳Q′ (par-left  tr)  = Σ-map (_∣ _)
                                         (Σ-map (map-⟶̂ par-left)
                                                (_∣-cong′ convert Q≳Q′))
                                     (left-to-right P≳P′ tr)
    lr P≳P′ Q≳Q′ (par-right tr)  = Σ-map (_ ∣_)
                                         (Σ-map (map-⟶̂ par-right)
                                                (convert P≳P′ ∣-cong′_))
                                     (left-to-right Q≳Q′ tr)
    lr P≳P′ Q≳Q′ (par-τ tr₁ tr₂) = Σ-zip _∣_
                                         (Σ-zip (zip-⟶̂ (λ ()) (λ _ ())
                                                       (λ ()) par-τ)
                                                _∣-cong′_)
                                     (left-to-right P≳P′ tr₁)
                                     (left-to-right Q≳Q′ tr₂)

  _∣-cong′_ : ∀ {i P P′ Q Q′} →
              [ i ] P ≳′ P′ → [ i ] Q ≳′ Q′ → [ i ] P ∣ Q ≳′ P′ ∣ Q′
  force (P≳P′ ∣-cong′ Q≳Q′) = force P≳P′ ∣-cong force Q≳Q′

-- _·_ preserves the expansion relation.

infix 12 _·-cong_ _·-cong′_

_·-cong_ : ∀ {i μ μ′ P P′} →
           μ ≡ μ′ → [ i ] P ≳ P′ → [ i ] μ · P ≳ μ′ · P′
_·-cong_ {i} {μ} {P = P} {P′} refl P≳P′ = ⟨ lr , CL.·-cong P≳P′ ⟩
  where
  lr : ∀ {Q μ″} →
       μ · P [ μ″ ]⟶ Q →
       ∃ λ Q′ → μ · P′ [ μ″ ]⟶̂ Q′ × [ i ] Q ≳′ Q′
  lr action = _ , ⟶→⟶̂ action , convert P≳P′

_·-cong′_ : ∀ {i μ μ′ P P′} →
            μ ≡ μ′ → [ i ] P ≳′ P′ → [ i ] μ · P ≳′ μ′ · P′
force (μ≡μ′ ·-cong′ P≳P′) = μ≡μ′ ·-cong force P≳P′

-- _· turns equal actions into processes related by the expansion
-- relation.

infix 12 _·-cong _·-cong′

_·-cong : ∀ {μ μ′} → μ ≡ μ′ → μ · ≳ μ′ ·
refl ·-cong = reflexive

_·-cong′ : ∀ {μ μ′} → μ ≡ μ′ → μ · ≳′ μ′ ·
refl ·-cong′ = reflexive

mutual

  -- ν preserves the expansion relation.

  ν-cong : ∀ {i a a′ P P′} →
           a ≡ a′ → [ i ] P ≳ P′ → [ i ] ν a P ≳ ν a′ P′
  ν-cong {i} {a} {P = P} {P′} refl P≳P′ =
    ⟨ lr
    , CL.ν-cong (ν-cong′ refl) P≳P′
    ⟩
    where
    lr : ∀ {Q μ} →
         ν a P [ μ ]⟶ Q →
         ∃ λ Q′ → ν a P′ [ μ ]⟶̂ Q′ × [ i ] Q ≳′ Q′
    lr {μ = μ} (restriction {P′ = Q} a∉μ P⟶Q)
      with left-to-right P≳P′ P⟶Q
    ... | Q′ , step P′⟶Q′ , Q≳′Q′ =
      ν a Q     ∼⟨ ν-cong′ refl Q≳′Q′ ⟩■
      ν a Q′
        ⟵̂[ μ ]  ←⟨ restriction a∉μ P′⟶Q′ ⟩■
      ν a P′

    ... | _ , done μs , Q≳′P′ =
      ν a Q     ∼⟨ ν-cong′ refl Q≳′P′ ⟩■
      ν a P′
        ⟵̂[ μ ]  ←⟨ ⟶̂: done μs ⟩■
      ν a P′

  ν-cong′ : ∀ {i a a′ P P′} →
            a ≡ a′ → [ i ] P ≳′ P′ → [ i ] ν a P ≳′ ν a′ P′
  force (ν-cong′ a≡a′ P≳P′) = ν-cong a≡a′ (force P≳P′)

mutual

  -- !_ preserves the expansion relation.

  infix 10 !-cong_ !-cong′_

  !-cong_ : ∀ {i P P′} →
            [ i ] P ≳ P′ → [ i ] ! P ≳ ! P′
  !-cong_ {i} {P} {P′} P≳P′ =
    ⟨ lr
    , CL.!-cong _∣-cong′_ !-cong′_ P≳P′
    ⟩
    where
    lr : ∀ {Q μ} →
         ! P [ μ ]⟶ Q →
         ∃ λ Q′ → ! P′ [ μ ]⟶̂ Q′ × [ i ] Q ≳′ Q′
    lr {Q} {μ} !P⟶Q = case S.6-1-3-2 !P⟶Q of λ where

      (inj₁ (P″ , P⟶P″ , Q∼!P∣P″)) → case left-to-right P≳P′ P⟶P″ of λ where
        (_ , done refl , P″≳′P′) →
          Q          ∼⟨ Q∼!P∣P″ ⟩
          ! P  ∣ P″  ∼′⟨ !-cong′ (convert P≳P′) ∣-cong′ P″≳′P′ ⟩ S.∼:
          ! P′ ∣ P′  ∼⟨ S.6-1-2 ⟩■
          ! P′
            ⟵̂[ τ ]
          ! P′       ■

        (Q′ , step P′⟶Q′ , P″≳′Q′) →
          Q          ∼⟨ Q∼!P∣P″ ⟩
          ! P  ∣ P″  ∼⟨ !-cong′ (convert P≳P′) ∣-cong′ P″≳′Q′ ⟩■
          ! P′ ∣ Q′
            ⟵̂[ μ ]   ←⟨ replication (par-right P′⟶Q′) ⟩■
          ! P′

      (inj₂ (refl , P″ , P‴ , a , P⟶P″ , P⟶P‴ , Q≳!P∣P″∣P‴)) →
        case left-to-right P≳P′ P⟶P″ ,′
             left-to-right P≳P′ P⟶P‴ of λ where
          ((Q′ , step P′⟶Q′ , P″≳′Q′) ,
           (Q″ , step P′⟶Q″ , P‴≳′Q″)) →
            Q                 ∼⟨ Q≳!P∣P″∣P‴ ⟩
            (! P ∣ P″) ∣ P‴   ∼⟨ (!-cong′ (convert P≳P′) ∣-cong′ P″≳′Q′) ∣-cong′ P‴≳′Q″ ⟩■
            (! P′ ∣ Q′) ∣ Q″
              ⟵̂[ μ ]          ←⟨ replication (par-τ (replication (par-right P′⟶Q′)) P′⟶Q″) ⟩■
            ! P′

          ((_ , done () , _) , _)
          (_ , (_ , done () , _))

  !-cong′_ : ∀ {i P P′} → [ i ] P ≳′ P′ → [ i ] ! P ≳′ ! P′
  force (!-cong′ P≳P′) = !-cong (force P≳P′)

-- It is not necessarily the case that, if P expands P′, then P ⊕ Q is
-- weakly bisimilar to P′ ⊕ Q (assuming that Name is inhabited).
--
-- I based the counterexample on one in "Enhancements of the
-- bisimulation proof method" by Pous and Sangiorgi.

¬⊕-congˡ-≳≈ : Name → ¬ (∀ {P P′ Q} → P ≳ P′ → P ⊕ Q ≈ P′ ⊕ Q)
¬⊕-congˡ-≳≈ x =
  (∀ {P P′ Q} → P ≳ P′ → P ⊕ Q ≈ P′ ⊕ Q)  ↝⟨ _$ τa≳a ⟩
  τ · (a ·) ⊕ b · ≈ a · ⊕ b ·             ↝⟨ τa⊕b≉a⊕b ⟩□
  ⊥                                       □
  where
  a = x , true
  b = x , false

  τa≳a : ∀ {a} → τ · (a ·) ≳ a ·
  τa≳a {a} =
    ⟨ (λ where
        action →
          a ·       ■
            ⟵̂[ τ ]
          a ·       ■)
    , (λ where
        action →
          τ · (a ·)      →⟨ ⟶: action ⟩
          a ·            →⟨ ⟶: action ⟩■
            ⇒̂[ name a ]
          ∅              ■)
    ⟩

  τa⊕b≉a⊕b : ¬ τ · (a ·) ⊕ b · ≈ a · ⊕ b ·
  τa⊕b≉a⊕b τa⊕b≈a⊕b
    with W.left-to-right τa⊕b≈a⊕b (choice-left action)
  ... | _ , non-silent ¬s _ , _ = ⊥-elim (¬s refl)
  ... | _ , silent refl (step () (choice-left  action) _) , _
  ... | _ , silent refl (step () (choice-right action) _) , _
  ... | _ , silent refl done , a≈′a⊕b
    with W.right-to-left (force a≈′a⊕b) (choice-right action)
  ...   | _ , silent () _ , _
  ...   | _ , non-silent _ (steps done () _) , _
  ...   | _ , non-silent _ (steps (step refl () _) _ _) , _

-- It is not necessarily the case that, if Q expands Q′, then P ⊕ Q is
-- weakly bisimilar to P ⊕ Q′ (assuming that Name is inhabited).

¬⊕-congʳ-≳≈ : Name → ¬ (∀ {P Q Q′} → Q ≳ Q′ → P ⊕ Q ≈ P ⊕ Q′)
¬⊕-congʳ-≳≈ x ⊕-congʳ-≳≈ = ¬⊕-congˡ-≳≈ x ⊕-congˡ-≳≈
  where
  ⊕-congˡ-≳≈ : ∀ {P P′ Q} → P ≳ P′ → P ⊕ Q ≈ P′ ⊕ Q
  ⊕-congˡ-≳≈ {P} {P′} {Q} P≳P′ =
    P ⊕ Q   ∼⟨ S.⊕-comm ⟩
    Q ⊕ P   ∼′⟨ ⊕-congʳ-≳≈ P≳P′ ⟩ S.∼:
    Q ⊕ P′  ∼⟨ S.⊕-comm ⟩■
    P′ ⊕ Q

-- _⊕_ does not, in general, preserve the expansion relation in its
-- first argument (assuming that Name is inhabited).

¬⊕-congˡ : Name → ¬ (∀ {P P′ Q} → P ≳ P′ → P ⊕ Q ≳ P′ ⊕ Q)
¬⊕-congˡ x =
  (∀ {P P′ Q} → P ≳ P′ → P ⊕ Q ≳ P′ ⊕ Q)  ↝⟨ W.≳⇒≈ ∘_ ⟩
  (∀ {P P′ Q} → P ≳ P′ → P ⊕ Q ≈ P′ ⊕ Q)  ↝⟨ ¬⊕-congˡ-≳≈ x ⟩□
  ⊥                                       □

-- _⊕_ does not, in general, preserve the expansion relation in its
-- second argument (assuming that Name is inhabited).

¬⊕-congʳ : Name → ¬ (∀ {P Q Q′} → Q ≳ Q′ → P ⊕ Q ≳ P ⊕ Q′)
¬⊕-congʳ x =
  (∀ {P Q Q′} → Q ≳ Q′ → P ⊕ Q ≳ P ⊕ Q′)  ↝⟨ W.≳⇒≈ ∘_ ⟩
  (∀ {P Q Q′} → Q ≳ Q′ → P ⊕ Q ≈ P ⊕ Q′)  ↝⟨ ¬⊕-congʳ-≳≈ x ⟩□
  ⊥                                       □

-- Some congruence lemmas for combinations of _⊕_ and _·_.

⊕·-cong : ∀ {i P μ Q Q′} →
          [ i ] Q ≳ Q′ → [ i ] P ⊕ μ · Q ≳ P ⊕ μ · Q′
⊕·-cong {i} {P} {μ} {Q} {Q′} Q≳Q′ =
  ⟨ lr , CL.⊕·-cong Q≳Q′ ⟩
  where
  lr : ∀ {R μ′} →
       P ⊕ μ · Q [ μ′ ]⟶ R →
       ∃ λ R′ → P ⊕ μ · Q′ [ μ′ ]⟶̂ R′ × [ i ] R ≳′ R′
  lr {R} {μ′} = λ where
    (choice-left P⟶R) →
      R           ■
        ⟵̂[ μ′ ]   ←⟨ choice-left P⟶R ⟩■
      P ⊕ μ · Q′

    (choice-right action) →
      Q           ∼⟨ Q≳Q′ ⟩■
      Q′
        ⟵̂[ μ ]    ←⟨ choice-right action ⟩■
      P ⊕ μ · Q′

⊕·-cong′ : ∀ {i P μ Q Q′} →
           [ i ] Q ≳ Q′ → [ i ] P ⊕ μ · Q ≳′ P ⊕ μ · Q′
force (⊕·-cong′ Q≳Q′) = ⊕·-cong Q≳Q′

·⊕-cong : ∀ {i P P′ μ Q} →
          [ i ] P ≳ P′ → [ i ] μ · P ⊕ Q ≳ μ · P′ ⊕ Q
·⊕-cong {P = P} {P′} {μ} {Q} P≳P′ =
  μ · P ⊕ Q   ∼⟨ S.⊕-comm ⟩
  Q ⊕ μ · P   ∼′⟨ ⊕·-cong P≳P′ ⟩ S.∼:
  Q ⊕ μ · P′  ∼⟨ S.⊕-comm ⟩■
  μ · P′ ⊕ Q

·⊕-cong′ : ∀ {i P P′ μ Q} →
           [ i ] P ≳ P′ → [ i ] μ · P ⊕ Q ≳′ μ · P′ ⊕ Q
force (·⊕-cong′ P≳P′) = ·⊕-cong P≳P′

infix 8 _·⊕·-cong_ _·⊕·-cong′_

_·⊕·-cong_ : ∀ {i μ₁ μ₂ P₁ P₁′ P₂ P₂′} →
             [ i ] P₁ ≳ P₁′ → [ i ] P₂ ≳ P₂′ →
             [ i ] μ₁ · P₁ ⊕ μ₂ · P₂ ≳ μ₁ · P₁′ ⊕ μ₂ · P₂′
_·⊕·-cong_ {i} {μ₁} {μ₂} {P₁} {P₁′} {P₂} {P₂′} P₁≳P₁′ P₂≳P₂′ =
  ⟨ lr , CL.·⊕·-cong P₁≳P₁′ P₂≳P₂′ ⟩
  where
  lr : ∀ {R μ} → μ₁ · P₁ ⊕ μ₂ · P₂ [ μ ]⟶ R →
       ∃ λ R′ → μ₁ · P₁′ ⊕ μ₂ · P₂′ [ μ ]⟶̂ R′ × [ i ] R ≳′ R′
  lr = λ where
    (choice-left action) →
      P₁                   ∼⟨ P₁≳P₁′ ⟩■
      P₁′
        ⟵̂[ μ₁ ]            ←⟨ choice-left action ⟩■
      μ₁ · P₁′ ⊕ μ₂ · P₂′

    (choice-right action) →
      P₂                   ∼⟨ P₂≳P₂′ ⟩■
      P₂′
        ⟵̂[ μ₂ ]            ←⟨ choice-right action ⟩■
      μ₁ · P₁′ ⊕ μ₂ · P₂′

_·⊕·-cong′_ : ∀ {i μ₁ μ₂ P₁ P₁′ P₂ P₂′} →
              [ i ] P₁ ≳′ P₁′ → [ i ] P₂ ≳′ P₂′ →
              [ i ] μ₁ · P₁ ⊕ μ₂ · P₂ ≳′ μ₁ · P₁′ ⊕ μ₂ · P₂′
force (P₁≳′P₁′ ·⊕·-cong′ P₂≳′P₂′) =
  force P₁≳′P₁′ ·⊕·-cong force P₂≳′P₂′

-- _[_] preserves the expansion relation for non-degenerate contexts.
-- (This result is related to Theorem 6.5.25 in "Enhancements of the
-- bisimulation proof method" by Pous and Sangiorgi.)

infix 5 _[_]-cong _[_]-cong′

_[_]-cong :
  ∀ {i n Ps Qs} {C : Context n} →
  Non-degenerate C → (∀ x → [ i ] Ps x ≳ Qs x) →
  [ i ] C [ Ps ] ≳ C [ Qs ]
_[_]-cong =
  flip $
    CL.[]-cong _∣-cong_ _·-cong_ ν-cong !-cong_
               ⊕·-cong ·⊕-cong _·⊕·-cong_

_[_]-cong′ :
  ∀ {i n Ps Qs} {C : Context n} →
  Non-degenerate C → (∀ x → [ i ] Ps x ≳′ Qs x) →
  [ i ] C [ Ps ] ≳′ C [ Qs ]
force (C [ Ps≳Qs ]-cong′) = C [ (λ x → force (Ps≳Qs x)) ]-cong
