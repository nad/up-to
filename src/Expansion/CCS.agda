------------------------------------------------------------------------
-- Lemmas related to expansion and CCS
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Expansion.CCS {ℓ} {Name : Set ℓ} where

open import Equality.Propositional
open import Prelude hiding (module W)

open import Function-universe equality-with-J hiding (_∘_)

import Bisimilarity.Coinductive.Equational-reasoning-instances
import Bisimilarity.Exercises.Coinductive.CCS as SE
import
  Bisimilarity.Weak.Coinductive.Other.Equational-reasoning-instances
open import Equational-reasoning
import Expansion.Equational-reasoning-instances
open import Labelled-transition-system.CCS Name
open import Relation

import Bisimilarity.Coinductive CCS as S
open import Bisimilarity.Coinductive CCS using (_∼_)
open import Bisimilarity.Weak.Coinductive.Other CCS as W
  using (_≈_; force)
open import Expansion CCS
import Labelled-transition-system.Equational-reasoning-instances CCS

-- Some lemmas used to prove the congruence lemmas below as well as
-- similar results in Bisimilarity.Weak.CCS.

module Cong-lemmas
  ({R} R′ : Proc ∞ → Proc ∞ → Set ℓ)
  ⦃ _ : Reflexive R′ ⦄
  ⦃ _ : Convertible R R′ ⦄
  ⦃ _ : Convertible R′ R′ ⦄
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
    R′ (force P₁) (force P₂) → μ · P₂ [ μ′ ]⟶ Q₂ →
    ∃ λ Q₁ → μ · P₁ [ μ′ ]⇒̂ Q₁ × R′ Q₁ Q₂
  ·-cong P₁≳P₂ action = _ , ⟶→⇒̂ action , P₁≳P₂

  ⟨ν⟩-cong :
    (∀ {a P P′} → R′ P P′ → R′ (⟨ν a ⟩ P) (⟨ν a ⟩ P′)) →
    ∀ {a μ P P′ Q′} →
    R P P′ → ⟨ν a ⟩ P′ [ μ ]⟶ Q′ →
    ∃ λ Q → ⟨ν a ⟩ P [ μ ]⇒̂ Q × R′ Q Q′
  ⟨ν⟩-cong ⟨ν⟩-cong′ {a} {μ} {P} P≳P′
           (restriction {P′ = Q′} a∉μ P′⟶Q′) =
    case right-to-left P≳P′ P′⟶Q′ of λ where
      (Q , P⇒̂Q , Q≳′Q′) →
        ⟨ν a ⟩ P   →⟨ map-⇒̂′ (restriction ∘ ∉τ) (restriction a∉μ) P⇒̂Q ⟩■
          ⇒̂[ μ ]′
        ⟨ν a ⟩ Q   ∼⟨ ⟨ν⟩-cong′ Q≳′Q′ ⟩■
        ⟨ν a ⟩ Q′

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
      , ((! P ∣ Q₂) ∣ Q₁  ∼⟨ SE.swap-rightmost ⟩■
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
    case SE.6-1-3-2 !P′⟶Q′ of λ where

      (inj₁ (P″ , P′⟶P″ , Q′∼!P′∣P″)) →
        case right-to-left P≳P′ P′⟶P″ of λ where
          (_ , silent μs done , P≳′P″) →
            ! P        →⟨ silent μs done ⟩■
              ⇒̂[ μ ]′
            ! P        ∼⟨ symmetric SE.6-1-2 ⟩
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
    R′ (force Q) (force Q′) → P ⊕ μ · Q′ [ μ′ ]⟶ S′ →
    ∃ λ S → P ⊕ μ · Q [ μ′ ]⇒̂ S × R′ S S′
  ⊕·-cong {P} {Q} {Q′} {S′} {μ} {μ′} Q≳Q′ = λ where
    (choice-left P⟶S′) →
      P ⊕ μ · Q   →⟨ choice-left P⟶S′ ⟩■
        ⇒̂[ μ′ ]′
      S′          ■

    (choice-right action) →
      P ⊕ μ · Q  →⟨ choice-right action ⟩■
        ⇒̂[ μ ]′
      force Q    ∼⟨ Q≳Q′ ⟩■
      force Q′

  ·⊕·-cong :
    ∀ {μ₁ μ₂ P₁ P₁′ P₂ P₂′ S′ μ} →
    R′ (force P₁) (force P₁′) → R′ (force P₂) (force P₂′) →
    μ₁ · P₁′ ⊕ μ₂ · P₂′ [ μ ]⟶ S′ →
    ∃ λ S → μ₁ · P₁ ⊕ μ₂ · P₂ [ μ ]⇒̂ S × R′ S S′
  ·⊕·-cong {μ₁} {μ₂} {P₁} {P₁′} {P₂} {P₂′} P₁≳P₁′ P₂≳P₂′ = λ where
    (choice-left action) →
      μ₁ · P₁ ⊕ μ₂ · P₂  →⟨ choice-left action ⟩■
        ⇒̂[ μ₁ ]′
      force P₁           ∼⟨ P₁≳P₁′ ⟩■
      force P₁′

    (choice-right action) →
      μ₁ · P₁ ⊕ μ₂ · P₂  →⟨ choice-right action ⟩■
        ⇒̂[ μ₂ ]′
      force P₂           ∼⟨ P₂≳P₂′ ⟩■
      force P₂′

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
                                                (_∣-cong′ convert {a = ℓ} Q≳Q′))
                                     (left-to-right P≳P′ tr)
    lr P≳P′ Q≳Q′ (par-right tr)  = Σ-map (_ ∣_)
                                         (Σ-map (map-⟶̂ par-right)
                                                (convert {a = ℓ} P≳P′ ∣-cong′_))
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

_·-cong_ :
  ∀ {i μ μ′ P P′} →
  μ ≡ μ′ → [ i ] force P ≳′ force P′ → [ i ] μ · P ≳ μ′ · P′
_·-cong_ {i} {μ} {P = P} {P′} refl P≳P′ = ⟨ lr , CL.·-cong P≳P′ ⟩
  where
  lr : ∀ {Q μ″} →
       μ · P [ μ″ ]⟶ Q →
       ∃ λ Q′ → μ · P′ [ μ″ ]⟶̂ Q′ × [ i ] Q ≳′ Q′
  lr action = _ , ⟶→⟶̂ action , P≳P′

_·-cong′_ :
  ∀ {i μ μ′ P P′} →
  μ ≡ μ′ → [ i ] force P ≳′ force P′ → [ i ] μ · P ≳′ μ′ · P′
force (μ≡μ′ ·-cong′ P≳P′) = μ≡μ′ ·-cong P≳P′

-- _∙_ preserves the expansion relation.

infix 12 _∙-cong_ _∙-cong′_

_∙-cong_ : ∀ {i μ μ′ P P′} →
           μ ≡ μ′ → [ i ] P ≳ P′ → [ i ] μ ∙ P ≳ μ′ ∙ P′
refl ∙-cong P≳P′ = refl ·-cong convert {a = ℓ} P≳P′

_∙-cong′_ : ∀ {i μ μ′ P P′} →
            μ ≡ μ′ → [ i ] P ≳′ P′ → [ i ] μ ∙ P ≳′ μ′ ∙ P′
force (μ≡μ′ ∙-cong′ P≳P′) = μ≡μ′ ∙-cong force P≳P′

-- _∙ turns equal actions into processes related by the expansion
-- relation.

infix 12 _∙-cong _∙-cong′

_∙-cong : ∀ {μ μ′} → μ ≡ μ′ → μ ∙ ≳ μ′ ∙
refl ∙-cong = reflexive

_∙-cong′ : ∀ {μ μ′} → μ ≡ μ′ → μ ∙ ≳′ μ′ ∙
refl ∙-cong′ = reflexive

mutual

  -- ⟨ν_⟩ preserves the expansion relation.

  ⟨ν_⟩-cong : ∀ {i a a′ P P′} →
              a ≡ a′ → [ i ] P ≳ P′ → [ i ] ⟨ν a ⟩ P ≳ ⟨ν a′ ⟩ P′
  ⟨ν_⟩-cong {i} {a} {P = P} {P′} refl P≳P′ =
    ⟨ lr
    , CL.⟨ν⟩-cong ⟨ν refl ⟩-cong′ P≳P′
    ⟩
    where
    lr : ∀ {Q μ} →
         ⟨ν a ⟩ P [ μ ]⟶ Q →
         ∃ λ Q′ → ⟨ν a ⟩ P′ [ μ ]⟶̂ Q′ × [ i ] Q ≳′ Q′
    lr {μ = μ} (restriction {P′ = Q} a∉μ P⟶Q)
      with left-to-right P≳P′ P⟶Q
    ... | Q′ , step P′⟶Q′ , Q≳′Q′ =
      ⟨ν a ⟩ Q   ∼⟨ ⟨ν refl ⟩-cong′ Q≳′Q′ ⟩■
      ⟨ν a ⟩ Q′
        ⟵̂[ μ ]   ←⟨ restriction a∉μ P′⟶Q′ ⟩■
      ⟨ν a ⟩ P′

    ... | _ , done μs , Q≳′P′ =
      ⟨ν a ⟩ Q   ∼⟨ ⟨ν refl ⟩-cong′ Q≳′P′ ⟩■
      ⟨ν a ⟩ P′
        ⟵̂[ μ ]   ←⟨ ⟶̂: done μs ⟩■
      ⟨ν a ⟩ P′

  ⟨ν_⟩-cong′ : ∀ {i a a′ P P′} →
               a ≡ a′ → [ i ] P ≳′ P′ → [ i ] ⟨ν a ⟩ P ≳′ ⟨ν a′ ⟩ P′
  force (⟨ν a≡a′ ⟩-cong′ P≳P′) = ⟨ν a≡a′ ⟩-cong (force P≳P′)

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
    lr {Q} {μ} !P⟶Q = case SE.6-1-3-2 !P⟶Q of λ where

      (inj₁ (P″ , P⟶P″ , Q∼!P∣P″)) → case left-to-right P≳P′ P⟶P″ of λ where
        (_ , done s , P″≳′P′) → case silent≡τ s of λ where
          refl →
            Q          ∼⟨ Q∼!P∣P″ ⟩
            ! P  ∣ P″  ∼′⟨ !-cong′ (convert {a = ℓ} P≳P′) ∣-cong′ P″≳′P′ ⟩ S.∼:
            ! P′ ∣ P′  ∼⟨ SE.6-1-2 ⟩■
            ! P′
              ⟵̂[ τ ]
            ! P′       ■

        (Q′ , step P′⟶Q′ , P″≳′Q′) →
          Q          ∼⟨ Q∼!P∣P″ ⟩
          ! P  ∣ P″  ∼⟨ !-cong′ (convert {a = ℓ} P≳P′) ∣-cong′ P″≳′Q′ ⟩■
          ! P′ ∣ Q′
            ⟵̂[ μ ]   ←⟨ replication (par-right P′⟶Q′) ⟩■
          ! P′

      (inj₂ (refl , P″ , P‴ , a , P⟶P″ , P⟶P‴ , Q≳!P∣P″∣P‴)) →
        case left-to-right P≳P′ P⟶P″ ,′
             left-to-right P≳P′ P⟶P‴ of λ where
          ((Q′ , step P′⟶Q′ , P″≳′Q′) ,
           (Q″ , step P′⟶Q″ , P‴≳′Q″)) →
            Q                 ∼⟨ Q≳!P∣P″∣P‴ ⟩
            (! P ∣ P″) ∣ P‴   ∼⟨ (!-cong′ (convert {a = ℓ} P≳P′) ∣-cong′ P″≳′Q′) ∣-cong′ P‴≳′Q″ ⟩■
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
  τ ∙ (a ∙) ⊕ b ∙ ≈ a ∙ ⊕ b ∙             ↝⟨ τa⊕b≉a⊕b ⟩□
  ⊥                                       □
  where
  a = x , true
  b = x , false

  τa≳a : ∀ {a} → τ ∙ (a ∙) ≳ a ∙
  τa≳a {a} =
    ⟨ (λ where
        action →
          a ∙       ■
            ⟵̂[ τ ]
          a ∙       ■)
    , (λ where
        action →
          τ ∙ (a ∙)      →⟨ ⟶: action ⟩
          a ∙            →⟨ ⟶: action ⟩■
            ⇒̂[ name a ]
          ∅              ■)
    ⟩

  τa⊕b≉a⊕b : ¬ τ ∙ (a ∙) ⊕ b ∙ ≈ a ∙ ⊕ b ∙
  τa⊕b≉a⊕b τa⊕b≈a⊕b
    with W.left-to-right τa⊕b≈a⊕b (choice-left action)
  ... | _ , non-silent ¬s _ , _ = ⊥-elim (¬s _)
  ... | _ , silent _ (step () (choice-left  action) _) , _
  ... | _ , silent _ (step () (choice-right action) _) , _
  ... | _ , silent _ done , a≈′a⊕b
    with W.right-to-left (force a≈′a⊕b) (choice-right action)
  ...   | _ , silent () _ , _
  ...   | _ , non-silent _ (steps done () _) , _
  ...   | _ , non-silent _ (steps (step () action _) _ _) , _

-- It is not necessarily the case that, if Q expands Q′, then P ⊕ Q is
-- weakly bisimilar to P ⊕ Q′ (assuming that Name is inhabited).

¬⊕-congʳ-≳≈ : Name → ¬ (∀ {P Q Q′} → Q ≳ Q′ → P ⊕ Q ≈ P ⊕ Q′)
¬⊕-congʳ-≳≈ x ⊕-congʳ-≳≈ = ¬⊕-congˡ-≳≈ x ⊕-congˡ-≳≈
  where
  ⊕-congˡ-≳≈ : ∀ {P P′ Q} → P ≳ P′ → P ⊕ Q ≈ P′ ⊕ Q
  ⊕-congˡ-≳≈ {P} {P′} {Q} P≳P′ =
    P ⊕ Q   ∼⟨ SE.⊕-comm ⟩
    Q ⊕ P   ∼′⟨ ⊕-congʳ-≳≈ P≳P′ ⟩ S.∼:
    Q ⊕ P′  ∼⟨ SE.⊕-comm ⟩■
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
          [ i ] force Q ≳′ force Q′ → [ i ] P ⊕ μ · Q ≳ P ⊕ μ · Q′
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
      force Q     ∼⟨ Q≳Q′ ⟩■
      force Q′
        ⟵̂[ μ ]    ←⟨ choice-right action ⟩■
      P ⊕ μ · Q′

⊕·-cong′ : ∀ {i P μ Q Q′} →
           [ i ] force Q ≳′ force Q′ → [ i ] P ⊕ μ · Q ≳′ P ⊕ μ · Q′
force (⊕·-cong′ Q≳Q′) = ⊕·-cong Q≳Q′

·⊕-cong : ∀ {i P P′ μ Q} →
          [ i ] force P ≳′ force P′ → [ i ] μ · P ⊕ Q ≳ μ · P′ ⊕ Q
·⊕-cong {P = P} {P′} {μ} {Q} P≳P′ =
  μ · P ⊕ Q   ∼⟨ SE.⊕-comm ⟩
  Q ⊕ μ · P   ∼′⟨ ⊕·-cong P≳P′ ⟩ S.∼:
  Q ⊕ μ · P′  ∼⟨ SE.⊕-comm ⟩■
  μ · P′ ⊕ Q

·⊕-cong′ : ∀ {i P P′ μ Q} →
           [ i ] force P ≳′ force P′ → [ i ] μ · P ⊕ Q ≳′ μ · P′ ⊕ Q
force (·⊕-cong′ P≳P′) = ·⊕-cong P≳P′

infix 8 _·⊕·-cong_ _·⊕·-cong′_

_·⊕·-cong_ :
  ∀ {i μ₁ μ₂ P₁ P₁′ P₂ P₂′} →
  [ i ] force P₁ ≳′ force P₁′ → [ i ] force P₂ ≳′ force P₂′ →
  [ i ] μ₁ · P₁ ⊕ μ₂ · P₂ ≳ μ₁ · P₁′ ⊕ μ₂ · P₂′
_·⊕·-cong_ {i} {μ₁} {μ₂} {P₁} {P₁′} {P₂} {P₂′} P₁≳P₁′ P₂≳P₂′ =
  ⟨ lr , CL.·⊕·-cong P₁≳P₁′ P₂≳P₂′ ⟩
  where
  lr : ∀ {R μ} → μ₁ · P₁ ⊕ μ₂ · P₂ [ μ ]⟶ R →
       ∃ λ R′ → μ₁ · P₁′ ⊕ μ₂ · P₂′ [ μ ]⟶̂ R′ × [ i ] R ≳′ R′
  lr = λ where
    (choice-left action) →
      force P₁             ∼⟨ P₁≳P₁′ ⟩■
      force P₁′
        ⟵̂[ μ₁ ]            ←⟨ choice-left action ⟩■
      μ₁ · P₁′ ⊕ μ₂ · P₂′

    (choice-right action) →
      force P₂             ∼⟨ P₂≳P₂′ ⟩■
      force P₂′
        ⟵̂[ μ₂ ]            ←⟨ choice-right action ⟩■
      μ₁ · P₁′ ⊕ μ₂ · P₂′

_·⊕·-cong′_ :
  ∀ {i μ₁ μ₂ P₁ P₁′ P₂ P₂′} →
  [ i ] force P₁ ≳′ force P₁′ → [ i ] force P₂ ≳′ force P₂′ →
  [ i ] μ₁ · P₁ ⊕ μ₂ · P₂ ≳′ μ₁ · P₁′ ⊕ μ₂ · P₂′
force (P₁≳′P₁′ ·⊕·-cong′ P₂≳′P₂′) = P₁≳′P₁′ ·⊕·-cong P₂≳′P₂′

-- _[_] preserves the expansion relation for non-degenerate contexts.
-- (This result is related to Theorem 6.5.25 in "Enhancements of the
-- bisimulation proof method" by Pous and Sangiorgi.)

infix 5 _[_]-cong _[_]-cong′

_[_]-cong :
  ∀ {i n Ps Qs} {C : Context ∞ n} →
  Non-degenerate ∞ C → (∀ x → [ i ] Ps x ≳ Qs x) →
  [ i ] C [ Ps ] ≳ C [ Qs ]
hole     [ Ps≳Qs ]-cong = Ps≳Qs _
∅        [ Ps≳Qs ]-cong = reflexive
D₁ ∣ D₂  [ Ps≳Qs ]-cong = (D₁ [ Ps≳Qs ]-cong) ∣-cong (D₂ [ Ps≳Qs ]-cong)
action D [ Ps≳Qs ]-cong = refl ·-cong λ { .force → force D [ Ps≳Qs ]-cong }
⟨ν⟩ D    [ Ps≳Qs ]-cong = ⟨ν refl ⟩-cong (D [ Ps≳Qs ]-cong)
! D      [ Ps≳Qs ]-cong = !-cong (D [ Ps≳Qs ]-cong)
D₁ ⊕ D₂  [ Ps≳Qs ]-cong = ⊕-cong Ps≳Qs D₁ D₂
  where
  _[_]-cong′ :
    ∀ {i n Ps Qs} {C : Context ∞ n} →
    Non-degenerate′ ∞ C → (∀ x → [ i ] Ps x ≳ Qs x) →
    [ i ] C [ Ps ] ≳′ C [ Qs ]
  force (D [ Ps≳Qs ]-cong′) = force D [ Ps≳Qs ]-cong

  ⊕-cong :
    ∀ {i n Ps Qs} {C₁ C₂ : Context ∞ n} →
    (∀ x → [ i ] Ps x ≳ Qs x) →
    Non-degenerate-summand ∞ C₁ →
    Non-degenerate-summand ∞ C₂ →
    [ i ] (C₁ [ Ps ]) ⊕ (C₂ [ Ps ]) ≳ (C₁ [ Qs ]) ⊕ (C₂ [ Qs ])
  ⊕-cong {Ps = Ps} {Qs} Ps≳Qs = λ where
    (process P₁) (process P₂) →
      (context P₁ [ Ps ]) ⊕ (context P₂ [ Ps ])  ∼⟨ symmetric (SE.≡→∼ (context-[] P₁) SE.⊕-cong SE.≡→∼ (context-[] P₂)) ⟩
      P₁ ⊕ P₂                                    ∼⟨ SE.≡→∼ (context-[] P₁) SE.⊕-cong SE.≡→∼ (context-[] P₂) ⟩■
      (context P₁ [ Qs ]) ⊕ (context P₂ [ Qs ])

    (process P₁) (action {μ = μ₂} {C = C₂} D₂) →
      (context P₁ [ Ps ]) ⊕ μ₂ · (C₂ [ Ps ]′)  ∼⟨ symmetric (SE.≡→∼ (context-[] P₁)) SE.⊕-cong (_ ■) ⟩
      P₁ ⊕ μ₂ · (C₂ [ Ps ]′)                   ∼′⟨ ⊕·-cong (D₂ [ Ps≳Qs ]-cong′) ⟩ S.∼:
      P₁ ⊕ μ₂ · (C₂ [ Qs ]′)                   ∼⟨ SE.≡→∼ (context-[] P₁) SE.⊕-cong (_ ■) ⟩■
      (context P₁ [ Qs ]) ⊕ μ₂ · (C₂ [ Qs ]′)

    (action {μ = μ₁} {C = C₁} D₁) (process P₂) →
      μ₁ · (C₁ [ Ps ]′) ⊕ (context P₂ [ Ps ])  ∼⟨ (_ ■) SE.⊕-cong symmetric (SE.≡→∼ (context-[] P₂)) ⟩
      μ₁ · (C₁ [ Ps ]′) ⊕ P₂                   ∼′⟨ ·⊕-cong (D₁ [ Ps≳Qs ]-cong′) ⟩ S.∼:
      μ₁ · (C₁ [ Qs ]′) ⊕ P₂                   ∼⟨ (_ ■) SE.⊕-cong SE.≡→∼ (context-[] P₂) ⟩■
      μ₁ · (C₁ [ Qs ]′) ⊕ (context P₂ [ Qs ])

    (action {μ = μ₁} {C = C₁} D₁) (action {μ = μ₂} {C = C₂} D₂) →
      μ₁ · (C₁ [ Ps ]′) ⊕ μ₂ · (C₂ [ Ps ]′)  ∼⟨ (D₁ [ Ps≳Qs ]-cong′) ·⊕·-cong (D₂ [ Ps≳Qs ]-cong′) ⟩■
      μ₁ · (C₁ [ Qs ]′) ⊕ μ₂ · (C₂ [ Qs ]′)

_[_]-cong′ :
  ∀ {i n Ps Qs} {C : Context ∞ n} →
  Non-degenerate ∞ C → (∀ x → [ i ] Ps x ≳′ Qs x) →
  [ i ] C [ Ps ] ≳′ C [ Qs ]
force (C [ Ps≳Qs ]-cong′) = C [ (λ x → force (Ps≳Qs x)) ]-cong
