------------------------------------------------------------------------
-- Lemmas related to expansion and CCS
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Expansion.CCS {Name : Set} where

open import Equality.Propositional
open import Prelude

open import Function-universe equality-with-J

open import Labelled-transition-system

open CCS Name
open LTS CCS hiding (_[_]⟶_)

import Bisimilarity.Coinductive CCS as S
import Bisimilarity.Coinductive.Equational-reasoning-instances
open import Bisimilarity.Coinductive CCS using (_∼_)
import Bisimilarity.Exercises.Coinductive as S
open import Equational-reasoning
open import Expansion CCS
import Expansion.Equational-reasoning-instances
import Labelled-transition-system.Equational-reasoning-instances CCS
  as Unused

mutual

  -- _∣_ preserves the expansion relation.

  infix 6 _∣-cong_ _∣-cong′_ _∣-cong′ˡ_ _∣-cong′ʳ_ _∣-cong′ˡʳ_

  _∣-cong_ : ∀ {i P P′ Q Q′} →
             [ i ] P ≳ P′ → [ i ] Q ≳ Q′ → [ i ] P ∣ Q ≳ P′ ∣ Q′
  _∣-cong_ {i} P≳P′ Q≳Q′ = ⟨ lr P≳P′ Q≳Q′ , rl P≳P′ Q≳Q′ ⟩
    where
    lr : ∀ {P P′ Q Q′ R μ} →
         [ i ] P ≳ P′ → [ i ] Q ≳ Q′ → P ∣ Q [ μ ]⟶ R →
         ∃ λ R′ → P′ ∣ Q′ [ μ ]⟶̂ R′ × [ i ] R ≳′ R′
    lr P≳P′ Q≳Q′ (par-left  tr)  = Σ-map (_∣ _)
                                         (Σ-map (map-⟶̂ par-left)
                                                (_∣-cong′ˡ Q≳Q′))
                                     (left-to-right P≳P′ tr)
    lr P≳P′ Q≳Q′ (par-right tr)  = Σ-map (_ ∣_)
                                         (Σ-map (map-⟶̂ par-right)
                                                (P≳P′ ∣-cong′ʳ_))
                                     (left-to-right Q≳Q′ tr)
    lr P≳P′ Q≳Q′ (par-τ tr₁ tr₂) = Σ-zip _∣_
                                         (Σ-zip (zip-⟶̂ (λ ()) (λ _ ())
                                                       (λ ()) par-τ)
                                                _∣-cong′ˡʳ_)
                                     (left-to-right P≳P′ tr₁)
                                     (left-to-right Q≳Q′ tr₂)

    rl : ∀ {P P′ Q Q′ R′ μ} →
         [ i ] P ≳ P′ → [ i ] Q ≳ Q′ → P′ ∣ Q′ [ μ ]⟶ R′ →
         ∃ λ R → P ∣ Q [ μ ]⇒̂ R × [ i ] R ≳′ R′
    rl P≳P′ Q≳Q′ (par-left  tr)  = Σ-map (_∣ _)
                                         (Σ-map (map-⇒̂ par-left)
                                                (_∣-cong′ˡ Q≳Q′))
                                     (right-to-left P≳P′ tr)
    rl P≳P′ Q≳Q′ (par-right tr)  = Σ-map (_ ∣_)
                                         (Σ-map (map-⇒̂ par-right)
                                                (P≳P′ ∣-cong′ʳ_))
                                     (right-to-left Q≳Q′ tr)
    rl P≳P′ Q≳Q′ (par-τ tr₁ tr₂) = Σ-zip _∣_
                                         (Σ-zip (zip-⇒̂ par-left
                                                       par-right (λ ())
                                                       (λ _ ()) (λ ())
                                                       par-τ)
                                                _∣-cong′ˡʳ_)
                                     (right-to-left P≳P′ tr₁)
                                     (right-to-left Q≳Q′ tr₂)

  _∣-cong′ˡ_ : ∀ {i P P′ Q Q′} →
               [ i ] P ≳′ P′ → [ i ] Q ≳ Q′ → [ i ] P ∣ Q ≳′ P′ ∣ Q′
  force (P≳P′ ∣-cong′ˡ Q≳Q′) = force P≳P′ ∣-cong Q≳Q′

  _∣-cong′ʳ_ : ∀ {i P P′ Q Q′} →
               [ i ] P ≳ P′ → [ i ] Q ≳′ Q′ → [ i ] P ∣ Q ≳′ P′ ∣ Q′
  force (P≳P′ ∣-cong′ʳ Q≳Q′) = P≳P′ ∣-cong force Q≳Q′

  _∣-cong′ˡʳ_ : ∀ {i P P′ Q Q′} →
                [ i ] P ≳′ P′ → [ i ] Q ≳′ Q′ → [ i ] P ∣ Q ≳′ P′ ∣ Q′
  force (P≳P′ ∣-cong′ˡʳ Q≳Q′) = force P≳P′ ∣-cong force Q≳Q′

_∣-cong′_ : ∀ {i P P′ Q Q′} →
            [ i ] P ≳ P′ → [ i ] Q ≳ Q′ → [ i ] P ∣ Q ≳′ P′ ∣ Q′
force (P≳P′ ∣-cong′ Q≳Q′) = P≳P′ ∣-cong Q≳Q′

-- _·_ preserves the expansion relation.

infix 12 _·-cong_ _·-cong′_ _·-cong″_

_·-cong_ : ∀ {i μ μ′ P P′} →
           μ ≡ μ′ → [ i ] P ≳ P′ → [ i ] μ · P ≳ μ′ · P′
_·-cong_ {i} {μ} {P = P} {P′} refl P≳P′ = ⟨ lr , rl ⟩
  where
  lr : ∀ {Q μ″} →
       μ · P [ μ″ ]⟶ Q →
       ∃ λ Q′ → μ · P′ [ μ″ ]⟶̂ Q′ × [ i ] Q ≳′ Q′
  lr action = _ , ⟶→⟶̂ action , convert P≳P′

  rl : ∀ {Q′ μ″} →
       μ · P′ [ μ″ ]⟶ Q′ →
       ∃ λ Q → μ · P [ μ″ ]⇒̂ Q × [ i ] Q ≳′ Q′
  rl action = _ , ⟶→⇒̂ action , convert P≳P′

_·-cong′_ : ∀ {i μ μ′ P P′} →
            μ ≡ μ′ → [ i ] P ≳ P′ → [ i ] μ · P ≳′ μ′ · P′
force (μ≡μ′ ·-cong′ P≳P′) = μ≡μ′ ·-cong P≳P′

_·-cong″_ : ∀ {i μ μ′ P P′} →
            μ ≡ μ′ → [ i ] P ≳′ P′ → [ i ] μ · P ≳′ μ′ · P′
force (μ≡μ′ ·-cong″ P≳P′) = μ≡μ′ ·-cong force P≳P′

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
  ν-cong {i} {a} {P = P} {P′} refl P≳P′ = ⟨ lr , rl ⟩
    where
    lr : ∀ {Q μ} →
         ν a P [ μ ]⟶ Q →
         ∃ λ Q′ → ν a P′ [ μ ]⟶̂ Q′ × [ i ] Q ≳′ Q′
    lr {μ = μ} (restriction {P′ = Q} a∉μ P⟶Q)
      with left-to-right P≳P′ P⟶Q
    ... | Q′ , step P′⟶Q′ , Q≳′Q′ =
      ν a Q     ∼⟨ ν-cong″ refl Q≳′Q′ ⟩■
      ν a Q′
        ⟵̂[ μ ]  ←⟨ restriction a∉μ P′⟶Q′ ⟩■
      ν a P′

    ... | _ , done μs , Q≳′P′ =
      ν a Q     ∼⟨ ν-cong″ refl Q≳′P′ ⟩■
      ν a P′
        ⟵̂[ μ ]  ←⟨ ⟶̂: done μs ⟩■
      ν a P′

    rl : ∀ {Q′ μ} →
         ν a P′ [ μ ]⟶ Q′ →
         ∃ λ Q → ν a P [ μ ]⇒̂ Q × [ i ] Q ≳′ Q′
    rl {μ = μ} (restriction {P′ = Q′} a∉μ P′⟶Q′)
      with right-to-left P≳P′ P′⟶Q′
    ... | Q , P⇒̂Q , Q≳′Q′ =
      ν a P     →⟨ map-⇒̂′ (λ { refl → restriction _ }) (restriction a∉μ) P⇒̂Q ⟩■
        ⇒̂[ μ ]
      ν a Q     ∼⟨ ν-cong″ refl Q≳′Q′ ⟩■
      ν a Q′

  ν-cong″ : ∀ {i a a′ P P′} →
            a ≡ a′ → [ i ] P ≳′ P′ → [ i ] ν a P ≳′ ν a′ P′
  force (ν-cong″ a≡a′ P≳P′) = ν-cong a≡a′ (force P≳P′)

ν-cong′ : ∀ {i a a′ P P′} →
          a ≡ a′ → [ i ] P ≳ P′ → [ i ] ν a P ≳′ ν a′ P′
force (ν-cong′ a≡a′ P≳P′) = ν-cong a≡a′ P≳P′

mutual

  -- !_ preserves the expansion relation.

  infix 10 !-cong_ !-cong′_ !-cong″_

  !-cong_ : ∀ {i P P′} →
            [ i ] P ≳ P′ → [ i ] ! P ≳ ! P′
  !-cong_ {i} {P} {P′} P≳P′ = ⟨ lr , rl ⟩
    where
    lr : ∀ {Q μ} →
         ! P [ μ ]⟶ Q →
         ∃ λ Q′ → ! P′ [ μ ]⟶̂ Q′ × [ i ] Q ≳′ Q′
    lr {Q} {μ} !P⟶Q with S.6-1-3-2 !P⟶Q

    ... | inj₁ (P″ , P⟶P″ , Q∼!P∣P″) with left-to-right P≳P′ P⟶P″
    ...   | _  , done refl , P″≳′P′ =
      Q          ∼⟨ Q∼!P∣P″ ⟩
      ! P  ∣ P″  ∼′⟨ !-cong′ P≳P′ ∣-cong′ˡʳ P″≳′P′ ⟩ S.∼:
      ! P′ ∣ P′  ∼⟨ S.6-1-2 ⟩■
      ! P′
        ⟵̂[ τ ]
      ! P′       ■

    ...   | Q′ , step P′⟶Q′ , P″≳′Q′ =
      Q          ∼⟨ Q∼!P∣P″ ⟩
      ! P  ∣ P″  ∼⟨ !-cong′ P≳P′ ∣-cong′ˡʳ P″≳′Q′ ⟩■
      ! P′ ∣ Q′
        ⟵̂[ μ ]   ←⟨ replication (par-right P′⟶Q′) ⟩■
      ! P′

    lr {Q} {μ} !P⟶Q
      | inj₂ (refl , P″ , P‴ , a , P⟶P″ , P⟶P‴ , Q≳!P∣P″∣P‴)
      with left-to-right P≳P′ P⟶P″ | left-to-right P≳P′ P⟶P‴
    ... | Q′ , step P′⟶Q′ , P″≳′Q′ | Q″ , step P′⟶Q″ , P‴≳′Q″ =
      Q                 ∼⟨ Q≳!P∣P″∣P‴ ⟩
      (! P ∣ P″) ∣ P‴   ∼⟨ (!-cong′ P≳P′ ∣-cong′ˡʳ P″≳′Q′) ∣-cong′ˡʳ P‴≳′Q″ ⟩■
      (! P′ ∣ Q′) ∣ Q″
        ⟵̂[ μ ]          ←⟨ replication (par-τ (replication (par-right P′⟶Q′)) P′⟶Q″) ⟩■
      ! P′

    ... | _ , done () , _ | _
    ... | _ | _ , done () , _

    rl-lemma₁ : ∀ {P Q μ} → P [ μ ]⇒ Q → ! P [ μ ]⇒ ! P ∣ Q
    rl-lemma₁ {P} {Q} {μ} = λ where
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

    rl-lemma₂ :
      ∀ {P Q₁ Q₂ a} →
      P [ name a ]⇒ Q₁ → P [ name (co a) ]⇒ Q₂ →
      ∃ λ R → ! P [ τ ]⇒ R × R ∼ (! P ∣ Q₁) ∣ Q₂
    rl-lemma₂ {P} {Q₁} {Q₂} {a} = λ where
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

    rl : ∀ {Q′ μ} →
         ! P′ [ μ ]⟶ Q′ →
         ∃ λ Q → ! P [ μ ]⇒̂ Q × [ i ] Q ≳′ Q′
    rl {Q′} {μ} !P′⟶Q′ with S.6-1-3-2 !P′⟶Q′

    ... | inj₁ (P″ , P′⟶P″ , Q′∼!P′∣P″) with right-to-left P≳P′ P′⟶P″
    ...   | _ , silent μs done , P≳′P″ =

      ! P        →⟨ silent μs done ⟩■
        ⇒̂[ μ ]
      ! P        ∼⟨ symmetric S.6-1-2 ⟩
      ! P ∣ P    ∼′⟨ !-cong′ P≳P′ ∣-cong′ˡʳ P≳′P″ ⟩ S.∼:
      ! P′ ∣ P″  ∼⟨ symmetric Q′∼!P′∣P″ ⟩■
      Q′

    ...   | Q , silent μs (step {q = R} {μ = μ′} μ′s P⟶R R⇒Q) , Q≳′P″ =
      ! P        →⟨ ⟶→⇒ μ′s (replication (par-right P⟶R)) ⟩
      ! P ∣ R    →⟨ silent μs (map-⇒ par-right R⇒Q) ⟩■
        ⇒̂[ μ ]
      ! P ∣ Q    ∼′⟨ !-cong′ P≳P′ ∣-cong′ˡʳ Q≳′P″ ⟩ S.∼:
      ! P′ ∣ P″  ∼⟨ symmetric Q′∼!P′∣P″ ⟩■
      Q′

    ...   | Q , non-silent ¬μs P⇒Q , Q≳′P″ =
      ! P        →⟨ non-silent ¬μs (rl-lemma₁ P⇒Q) ⟩■
        ⇒̂[ μ ]
      ! P ∣ Q    ∼′⟨ !-cong′ P≳P′ ∣-cong′ˡʳ Q≳′P″ ⟩ S.∼:
      ! P′ ∣ P″  ∼⟨ symmetric Q′∼!P′∣P″ ⟩■
      Q′

    rl {Q′} !P′⟶Q′
      | inj₂ (refl , P″ , P‴ , a , P′⟶P″ , P′⟶P‴ , Q′∼!P′∣P″∣P‴)
      with right-to-left P≳P′ P′⟶P″ | right-to-left P≳P′ P′⟶P‴
    ... | _ , silent () _ , _ | _
    ... | _ | _ , silent () _ , _

    ... | Q₁ , non-silent _ P⇒Q₁ , Q₁≳′P″
        | Q₂ , non-silent _ P⇒Q₂ , Q₂≳′P‴ with rl-lemma₂ P⇒Q₁ P⇒Q₂
    ...   | R , !P⇒R , R∼[!P∣Q₁]∣Q₂ =
      ! P               →⟨ !P⇒R ⟩■
        ⇒̂[ τ ]
      R                 ∼⟨ R∼[!P∣Q₁]∣Q₂ ⟩
      (! P ∣ Q₁) ∣ Q₂   ∼′⟨ ≳′: (!-cong′ P≳P′ ∣-cong′ˡʳ Q₁≳′P″) ∣-cong′ˡʳ Q₂≳′P‴ ⟩ S.∼:
      (! P′ ∣ P″) ∣ P‴  ∼⟨ symmetric Q′∼!P′∣P″∣P‴ ⟩■
      Q′

  !-cong′_ : ∀ {i P P′} → [ i ] P ≳ P′ → [ i ] ! P ≳′ ! P′
  force (!-cong′ P≳P′) = !-cong P≳P′

!-cong″_ : ∀ {i P P′} → [ i ] P ≳′ P′ → [ i ] ! P ≳′ ! P′
force (!-cong″ P≳P′) = !-cong force P≳P′

-- _⊕_ does not preserve the expansion relation in its first argument
-- (assuming that Name is inhabited).
--
-- I based the counterexample on one in "Enhancements of the
-- bisimulation proof method" by Pous and Sangiorgi.

¬⊕-congˡ : Name → ¬ (∀ {P P′ Q} → P ≳ P′ → P ⊕ Q ≳ P′ ⊕ Q)
¬⊕-congˡ x =
  (∀ {P P′ Q} → P ≳ P′ → P ⊕ Q ≳ P′ ⊕ Q)  ↝⟨ _$ τa≳a ⟩
  τ · (a ·) ⊕ b · ≳ a · ⊕ b ·             ↝⟨ τa⊕b≵a⊕b ⟩□
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

  τa⊕b≵a⊕b : ¬ τ · (a ·) ⊕ b · ≳ a · ⊕ b ·
  τa⊕b≵a⊕b τa⊕b≳a⊕b
    with left-to-right τa⊕b≳a⊕b (choice-left action)
  ... | _ , step (choice-left ()) , _
  ... | _ , step (choice-right ()) , _
  ... | _ , done refl , a≳′a⊕b
    with right-to-left (force a≳′a⊕b) (choice-right action)
  ...   | _ , silent () _ , _
  ...   | _ , non-silent _ (steps done () _) , _
  ...   | _ , non-silent _ (steps (step refl () _) _ _) , _

-- _⊕_ does not preserve the expansion relation in its second argument.
-- (assuming that Name is inhabited).

¬⊕-congʳ : Name → ¬ (∀ {P Q Q′} → Q ≳ Q′ → P ⊕ Q ≳ P ⊕ Q′)
¬⊕-congʳ x ⊕-congʳ = ¬⊕-congˡ x ⊕-congˡ
  where
  ⊕-congˡ : ∀ {P P′ Q} → P ≳ P′ → P ⊕ Q ≳ P′ ⊕ Q
  ⊕-congˡ {P} {P′} {Q} P≳P′ =
    P ⊕ Q   ∼⟨ S.⊕-comm ⟩
    Q ⊕ P   ∼′⟨ ⊕-congʳ P≳P′ ⟩ S.∼:
    Q ⊕ P′  ∼⟨ S.⊕-comm ⟩■
    P′ ⊕ Q

-- Some congruence lemmas for combinations of _⊕_ and _·_.

⊕·-cong : ∀ {i P μ Q Q′} →
          [ i ] Q ≳ Q′ → [ i ] P ⊕ μ · Q ≳ P ⊕ μ · Q′
⊕·-cong {i} {P} {μ} {Q} {Q′} Q≳Q′ = ⟨ lr , rl ⟩
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

  rl : ∀ {R′ μ′} →
       P ⊕ μ · Q′ [ μ′ ]⟶ R′ →
       ∃ λ R → P ⊕ μ · Q [ μ′ ]⇒̂ R × [ i ] R ≳′ R′
  rl {R′} {μ′} = λ where
    (choice-left P⟶R′) →
      P ⊕ μ · Q  →⟨ choice-left P⟶R′ ⟩■
        ⇒̂[ μ′ ]
      R′         ■

    (choice-right action) →
      P ⊕ μ · Q  →⟨ choice-right action ⟩■
        ⇒̂[ μ ]
      Q          ∼⟨ Q≳Q′ ⟩■
      Q′

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

infix 8 _·⊕·-cong_ _·⊕·-cong′_ _·⊕·-cong′ˡ_ _·⊕·-cong′ʳ_ _·⊕·-cong′ˡʳ_

_·⊕·-cong_ : ∀ {i μ₁ μ₂ P₁ P₁′ P₂ P₂′} →
             [ i ] P₁ ≳ P₁′ → [ i ] P₂ ≳ P₂′ →
             [ i ] μ₁ · P₁ ⊕ μ₂ · P₂ ≳ μ₁ · P₁′ ⊕ μ₂ · P₂′
_·⊕·-cong_ {i} {μ₁} {μ₂} {P₁} {P₁′} {P₂} {P₂′} P₁≳P₁′ P₂≳P₂′ =
  ⟨ lr , rl ⟩
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

  rl : ∀ {R′ μ} → μ₁ · P₁′ ⊕ μ₂ · P₂′ [ μ ]⟶ R′ →
       ∃ λ R → μ₁ · P₁ ⊕ μ₂ · P₂ [ μ ]⇒̂ R × [ i ] R ≳′ R′
  rl = λ where
    (choice-left action) →
      μ₁ · P₁ ⊕ μ₂ · P₂  →⟨ choice-left action ⟩■
        ⇒̂[ μ₁ ]
      P₁                 ∼⟨ P₁≳P₁′ ⟩■
      P₁′

    (choice-right action) →
      μ₁ · P₁ ⊕ μ₂ · P₂  →⟨ choice-right action ⟩■
        ⇒̂[ μ₂ ]
      P₂                 ∼⟨ P₂≳P₂′ ⟩■
      P₂′

_·⊕·-cong′_ : ∀ {i μ₁ μ₂ P₁ P₁′ P₂ P₂′} →
              [ i ] P₁ ≳ P₁′ → [ i ] P₂ ≳ P₂′ →
              [ i ] μ₁ · P₁ ⊕ μ₂ · P₂ ≳′ μ₁ · P₁′ ⊕ μ₂ · P₂′
force (P₁≳P₁′ ·⊕·-cong′ P₂≳P₂′) = P₁≳P₁′ ·⊕·-cong P₂≳P₂′

_·⊕·-cong′ˡ_ : ∀ {i μ₁ μ₂ P₁ P₁′ P₂ P₂′} →
               [ i ] P₁ ≳′ P₁′ → [ i ] P₂ ≳ P₂′ →
               [ i ] μ₁ · P₁ ⊕ μ₂ · P₂ ≳′ μ₁ · P₁′ ⊕ μ₂ · P₂′
force (P₁≳′P₁′ ·⊕·-cong′ˡ P₂≳P₂′) = force P₁≳′P₁′ ·⊕·-cong P₂≳P₂′

_·⊕·-cong′ʳ_ : ∀ {i μ₁ μ₂ P₁ P₁′ P₂ P₂′} →
               [ i ] P₁ ≳ P₁′ → [ i ] P₂ ≳′ P₂′ →
               [ i ] μ₁ · P₁ ⊕ μ₂ · P₂ ≳′ μ₁ · P₁′ ⊕ μ₂ · P₂′
force (P₁≳P₁′ ·⊕·-cong′ʳ P₂≳′P₂′) = P₁≳P₁′ ·⊕·-cong force P₂≳′P₂′

_·⊕·-cong′ˡʳ_ : ∀ {i μ₁ μ₂ P₁ P₁′ P₂ P₂′} →
                [ i ] P₁ ≳′ P₁′ → [ i ] P₂ ≳′ P₂′ →
                [ i ] μ₁ · P₁ ⊕ μ₂ · P₂ ≳′ μ₁ · P₁′ ⊕ μ₂ · P₂′
force (P₁≳′P₁′ ·⊕·-cong′ˡʳ P₂≳′P₂′) =
  force P₁≳′P₁′ ·⊕·-cong force P₂≳′P₂′

-- _[_] preserves the expansion relation for non-degenerate contexts.
-- (This result is related to Theorem 6.5.25 in "Enhancements of the
-- bisimulation proof method" by Pous and Sangiorgi.)

mutual

  infix 5 _[_]-cong _[_]-cong′ _[_]-cong″

  _[_]-cong :
    ∀ {i n Ps Qs} {C : Context n} →
    Non-degenerate C → (∀ x → [ i ] Ps x ≳ Qs x) →
    [ i ] C [ Ps ] ≳ C [ Qs ]
  hole     [ Ps≳Qs ]-cong = Ps≳Qs _
  ∅        [ Ps≳Qs ]-cong = reflexive
  D₁ ∣ D₂  [ Ps≳Qs ]-cong = (D₁ [ Ps≳Qs ]-cong) ∣-cong
                            (D₂ [ Ps≳Qs ]-cong)
  D₁ ⊕ D₂  [ Ps≳Qs ]-cong = ⟨ D₁ ⊕ D₂ ⟩[ Ps≳Qs ]-cong
  action D [ Ps≳Qs ]-cong = refl ·-cong (D [ Ps≳Qs ]-cong)
  ν D      [ Ps≳Qs ]-cong = ν-cong refl (D [ Ps≳Qs ]-cong)
  ! D      [ Ps≳Qs ]-cong = !-cong (D [ Ps≳Qs ]-cong)

  ⟨_⊕_⟩[_]-cong :
    ∀ {i n Ps Qs} {C₁ C₂ : Context n} →
    Non-degenerate-summand C₁ →
    Non-degenerate-summand C₂ →
    (∀ x → [ i ] Ps x ≳ Qs x) →
    [ i ] (C₁ [ Ps ]) ⊕ (C₂ [ Ps ]) ≳ (C₁ [ Qs ]) ⊕ (C₂ [ Qs ])
  ⟨_⊕_⟩[_]-cong {Ps = Ps} {Qs} = λ where
    (process P₁) (process P₂) Ps≳Qs →
      (context P₁ [ Ps ]) ⊕ (context P₂ [ Ps ])  ∼≡⟨ cong₂ _⊕_ (context-[] P₁) (context-[] P₂) ⟩
      P₁ ⊕ P₂                                    ∼≡⟨ sym $ cong₂ _⊕_ (context-[] P₁) (context-[] P₂) ⟩
      (context P₁ [ Qs ]) ⊕ (context P₂ [ Qs ])  ■

    (process P₁) (action {μ = μ₂} {C = C₂} D₂) Ps≳Qs →
      (context P₁ [ Ps ]) ⊕ (μ₂ · C₂ [ Ps ])  ∼≡⟨ cong (_⊕ _) (context-[] P₁) ⟩
      P₁ ⊕ (μ₂ · C₂ [ Ps ])                   ∼′⟨ ⊕·-cong (D₂ [ Ps≳Qs ]-cong) ⟩ S.∼:
      P₁ ⊕ (μ₂ · C₂ [ Qs ])                   ∼≡⟨ sym $ cong (_⊕ _) (context-[] P₁) ⟩
      (context P₁ [ Qs ]) ⊕ (μ₂ · C₂ [ Qs ])  ■

    (action {μ = μ₁} {C = C₁} D₁) (process P₂) Ps≳Qs →
      (μ₁ · C₁ [ Ps ]) ⊕ (context P₂ [ Ps ])  ∼≡⟨ cong (_ ⊕_) (context-[] P₂) ⟩
      (μ₁ · C₁ [ Ps ]) ⊕ P₂                   ∼′⟨ ·⊕-cong (D₁ [ Ps≳Qs ]-cong) ⟩ S.∼:
      (μ₁ · C₁ [ Qs ]) ⊕ P₂                   ∼≡⟨ sym $ cong (_ ⊕_) (context-[] P₂) ⟩
      (μ₁ · C₁ [ Qs ]) ⊕ (context P₂ [ Qs ])  ■

    (action {μ = μ₁} {C = C₁} D₁) (action {μ = μ₂} {C = C₂} D₂) Ps≳Qs →
      (μ₁ · C₁ [ Ps ]) ⊕ (μ₂ · C₂ [ Ps ])  ∼⟨ (D₁ [ Ps≳Qs ]-cong) ·⊕·-cong (D₂ [ Ps≳Qs ]-cong) ⟩■
      (μ₁ · C₁ [ Qs ]) ⊕ (μ₂ · C₂ [ Qs ])

_[_]-cong′ :
  ∀ {i n Ps Qs} {C : Context n} →
  Non-degenerate C → (∀ x → [ i ] Ps x ≳ Qs x) →
  [ i ] C [ Ps ] ≳′ C [ Qs ]
force (C [ Ps≳Qs ]-cong′) = C [ Ps≳Qs ]-cong

_[_]-cong″ :
  ∀ {i n Ps Qs} {C : Context n} →
  Non-degenerate C → (∀ x → [ i ] Ps x ≳′ Qs x) →
  [ i ] C [ Ps ] ≳′ C [ Qs ]
force (C [ Ps≳Qs ]-cong″) = C [ (λ x → force (Ps≳Qs x)) ]-cong
