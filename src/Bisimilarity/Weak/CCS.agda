------------------------------------------------------------------------
-- Lemmas related to weak bisimilarity and CCS
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Bisimilarity.Weak.CCS {ℓ} {Name : Set ℓ} where

open import Equality.Propositional
open import Prelude

open import Function-universe equality-with-J hiding (id; _∘_)

import Bisimilarity.Equational-reasoning-instances
import Bisimilarity.Exercises.Coinductive.CCS as SE
import Bisimilarity.Weak.Equational-reasoning-instances
open import Equational-reasoning
import Expansion.CCS as E
import Expansion.Equational-reasoning-instances
open import Labelled-transition-system.CCS Name

import Bisimilarity CCS as S
open import Bisimilarity.Weak CCS
open import Expansion CCS using (_≳_; ≳:_)
import Labelled-transition-system.Equational-reasoning-instances CCS

-- An instantiation of a module with helper lemmas.

private
  module CL {i} =
    E.Cong-lemmas
      [ i ]_≈′_ right-to-left (⇒̂→[]⇒ (λ ())) ⇒→⇒̂
      map-⇒̂ map-⇒̂′ zip-⇒̂
      (λ hyp {P Q} → λ where

        (silent s done) →
            _
          , (! P      →⟨ silent s done ⟩■)
          , (! P      ∼⟨ symmetric SE.6-1-2 ⟩
             ! P ∣ P  ∼≡⟨ refl ⟩■
             ! P ∣ Q)

        (silent s (step {q = R} s′ P⟶R R⇒Q)) →
            _
          , (! P      →⟨ ⟶→⇒ s′ (replication (par-right P⟶R)) ⟩
             ! P ∣ R  →⟨ silent s (map-⇒ par-right R⇒Q) ⟩■)
          , (! P ∣ Q  ■)

        (non-silent ¬s P⇒Q) →
            _
          , (! P  →⟨ non-silent ¬s (hyp P⇒Q) ⟩■)
          , (! P ∣ Q  ■))

mutual

  -- _∣_ preserves weak bisimilarity.

  infix 6 _∣-cong_ _∣-cong′_

  _∣-cong_ : ∀ {i P P′ Q Q′} →
             [ i ] P ≈ P′ → [ i ] Q ≈ Q′ → [ i ] P ∣ Q ≈ P′ ∣ Q′
  P≈P′ ∣-cong Q≈Q′ =
    ⟨ Σ-map id (Σ-map id symmetric) ∘
      rl (symmetric P≈P′) (symmetric Q≈Q′)
    , rl P≈P′ Q≈Q′
    ⟩
    where
    rl = CL.∣-cong _∣-cong′_

  _∣-cong′_ : ∀ {i P P′ Q Q′} →
              [ i ] P ≈′ P′ → [ i ] Q ≈′ Q′ → [ i ] P ∣ Q ≈′ P′ ∣ Q′
  force (P≈P′ ∣-cong′ Q≈Q′) = force P≈P′ ∣-cong force Q≈Q′

-- _·_ preserves weak bisimilarity.

infix 12 _·-cong_ _·-cong′_

_·-cong_ :
  ∀ {i μ μ′ P P′} →
  μ ≡ μ′ → [ i ] force P ≈′ force P′ → [ i ] μ · P ≈ μ′ · P′
refl ·-cong P≈P′ =
  ⟨ Σ-map id (Σ-map id symmetric) ∘ rl (symmetric P≈P′)
  , rl P≈P′
  ⟩
  where
  rl = CL.·-cong

_·-cong′_ :
  ∀ {i μ μ′ P P′} →
  μ ≡ μ′ → [ i ] force P ≈′ force P′ → [ i ] μ · P ≈′ μ′ · P′
force (μ≡μ′ ·-cong′ P≈P′) = μ≡μ′ ·-cong P≈P′

-- _∙_ preserves weak bisimilarity.

infix 12 _∙-cong_ _∙-cong′_

_∙-cong_ : ∀ {i μ μ′ P P′} →
           μ ≡ μ′ → [ i ] P ≈ P′ → [ i ] μ ∙ P ≈ μ′ ∙ P′
refl ∙-cong P≈P′ = refl ·-cong convert {a = ℓ} P≈P′

_∙-cong′_ : ∀ {i μ μ′ P P′} →
            μ ≡ μ′ → [ i ] P ≈′ P′ → [ i ] μ ∙ P ≈′ μ′ ∙ P′
force (μ≡μ′ ∙-cong′ P≈P′) = μ≡μ′ ∙-cong force P≈P′

-- _∙ turns equal actions into weakly bisimilar processes.

infix 12 _∙-cong _∙-cong′

_∙-cong : ∀ {μ μ′} → μ ≡ μ′ → μ ∙ ≈ μ′ ∙
refl ∙-cong = reflexive

_∙-cong′ : ∀ {μ μ′} → μ ≡ μ′ → μ ∙ ≈′ μ′ ∙
refl ∙-cong′ = reflexive

mutual

  -- ⟨ν_⟩ preserves weak bisimilarity.

  ⟨ν_⟩-cong : ∀ {i a a′ P P′} →
              a ≡ a′ → [ i ] P ≈ P′ → [ i ] ⟨ν a ⟩ P ≈ ⟨ν a′ ⟩ P′
  ⟨ν_⟩-cong {i} {a} {P = P} {P′} refl P≈P′ =
    ⟨ Σ-map id (Σ-map id symmetric) ∘
      CL.⟨ν⟩-cong ⟨ν refl ⟩-cong′ (symmetric P≈P′)
    , CL.⟨ν⟩-cong ⟨ν refl ⟩-cong′ P≈P′
    ⟩

  ⟨ν_⟩-cong′ : ∀ {i a a′ P P′} →
               a ≡ a′ → [ i ] P ≈′ P′ → [ i ] ⟨ν a ⟩ P ≈′ ⟨ν a′ ⟩ P′
  force (⟨ν a≡a′ ⟩-cong′ P≈P′) = ⟨ν a≡a′ ⟩-cong (force P≈P′)

mutual

  -- !_ preserves weak bisimilarity.

  infix 10 !-cong_ !-cong′_

  !-cong_ : ∀ {i P P′} →
            [ i ] P ≈ P′ → [ i ] ! P ≈ ! P′
  !-cong_ {i} {P} {P′} P≈P′ =
    ⟨ Σ-map id (Σ-map id symmetric) ∘
      CL.!-cong _∣-cong′_ !-cong′_ (symmetric P≈P′)
    , CL.!-cong _∣-cong′_ !-cong′_ P≈P′
    ⟩

  !-cong′_ : ∀ {i P P′} → [ i ] P ≈′ P′ → [ i ] ! P ≈′ ! P′
  force (!-cong′ P≈P′) = !-cong (force P≈P′)

-- _⊕_ does not, in general, preserve weak bisimilarity in its first
-- argument (assuming that Name is inhabited).

¬⊕-congˡ : Name → ¬ (∀ {P P′ Q} → P ≈ P′ → P ⊕ Q ≈ P′ ⊕ Q)
¬⊕-congˡ x =
  (∀ {P P′ Q} → P ≈ P′ → P ⊕ Q ≈ P′ ⊕ Q)  ↝⟨ _∘ ≳⇒≈ ⟩
  (∀ {P P′ Q} → P ≳ P′ → P ⊕ Q ≈ P′ ⊕ Q)  ↝⟨ E.¬⊕-congˡ-≳≈ x ⟩□
  ⊥                                       □

-- _⊕_ does not, in general, preserve weak bisimilarity in its second
-- argument (assuming that Name is inhabited).

¬⊕-congʳ : Name → ¬ (∀ {P Q Q′} → Q ≈ Q′ → P ⊕ Q ≈ P ⊕ Q′)
¬⊕-congʳ x =
  (∀ {P Q Q′} → Q ≈ Q′ → P ⊕ Q ≈ P ⊕ Q′)  ↝⟨ _∘ ≳⇒≈ ⟩
  (∀ {P Q Q′} → Q ≳ Q′ → P ⊕ Q ≈ P ⊕ Q′)  ↝⟨ E.¬⊕-congʳ-≳≈ x ⟩□
  ⊥                                       □

-- Some congruence lemmas for combinations of _⊕_ and _·_.

⊕·-cong :
  ∀ {i P μ Q Q′} →
  [ i ] force Q ≈′ force Q′ → [ i ] P ⊕ μ · Q ≈ P ⊕ μ · Q′
⊕·-cong Q≈Q′ =
  ⟨ Σ-map id (Σ-map id symmetric) ∘ CL.⊕·-cong (symmetric Q≈Q′)
  , CL.⊕·-cong Q≈Q′
  ⟩

⊕·-cong′ :
  ∀ {i P μ Q Q′} →
  [ i ] force Q ≈′ force Q′ → [ i ] P ⊕ μ · Q ≈′ P ⊕ μ · Q′
force (⊕·-cong′ Q≈Q′) = ⊕·-cong Q≈Q′

·⊕-cong : ∀ {i P P′ μ Q} →
          [ i ] force P ≈′ force P′ → [ i ] μ · P ⊕ Q ≈ μ · P′ ⊕ Q
·⊕-cong {P = P} {P′} {μ} {Q} P≈P′ =
  μ · P ⊕ Q   ∼⟨ SE.⊕-comm ⟩
  Q ⊕ μ · P   ∼′⟨ ⊕·-cong P≈P′ ⟩ S.∼:
  Q ⊕ μ · P′  ∼⟨ SE.⊕-comm ⟩■
  μ · P′ ⊕ Q

·⊕-cong′ :
  ∀ {i P P′ μ Q} →
  [ i ] force P ≈′ force P′ → [ i ] μ · P ⊕ Q ≈′ μ · P′ ⊕ Q
force (·⊕-cong′ P≈P′) = ·⊕-cong P≈P′

infix 8 _·⊕·-cong_ _·⊕·-cong′_

_·⊕·-cong_ :
  ∀ {i μ₁ μ₂ P₁ P₁′ P₂ P₂′} →
  [ i ] force P₁ ≈′ force P₁′ → [ i ] force P₂ ≈′ force P₂′ →
  [ i ] μ₁ · P₁ ⊕ μ₂ · P₂ ≈ μ₁ · P₁′ ⊕ μ₂ · P₂′
P₁≈P₁′ ·⊕·-cong P₂≈P₂′ =
  ⟨ Σ-map id (Σ-map id symmetric) ∘
    CL.·⊕·-cong (symmetric P₁≈P₁′) (symmetric P₂≈P₂′)
  , CL.·⊕·-cong P₁≈P₁′ P₂≈P₂′
  ⟩

_·⊕·-cong′_ :
  ∀ {i μ₁ μ₂ P₁ P₁′ P₂ P₂′} →
  [ i ] force P₁ ≈′ force P₁′ → [ i ] force P₂ ≈′ force P₂′ →
  [ i ] μ₁ · P₁ ⊕ μ₂ · P₂ ≈′ μ₁ · P₁′ ⊕ μ₂ · P₂′
force (P₁≈′P₁′ ·⊕·-cong′ P₂≈′P₂′) = P₁≈′P₁′ ·⊕·-cong P₂≈′P₂′

-- _[_] preserves weak bisimilarity for non-degenerate contexts. (This
-- result is similar to Theorem 6.5.25 in "Enhancements of the
-- bisimulation proof method" by Pous and Sangiorgi.)
--
-- TODO: This definition is very similar to E._[_]-cong. Find some way
-- to reduce the code duplication. (There was much less code
-- duplication before contexts were made coinductive.)

infix 5 _[_]-cong _[_]-cong′

_[_]-cong :
  ∀ {i n Ps Qs} {C : Context ∞ n} →
  Non-degenerate ∞ C → (∀ x → [ i ] Ps x ≈ Qs x) →
  [ i ] C [ Ps ] ≈ C [ Qs ]
hole     [ Ps≈Qs ]-cong = Ps≈Qs _
∅        [ Ps≈Qs ]-cong = reflexive
D₁ ∣ D₂  [ Ps≈Qs ]-cong = (D₁ [ Ps≈Qs ]-cong) ∣-cong (D₂ [ Ps≈Qs ]-cong)
action D [ Ps≈Qs ]-cong = refl ·-cong λ { .force → force D [ Ps≈Qs ]-cong }
⟨ν⟩ D    [ Ps≈Qs ]-cong = ⟨ν refl ⟩-cong (D [ Ps≈Qs ]-cong)
! D      [ Ps≈Qs ]-cong = !-cong (D [ Ps≈Qs ]-cong)
D₁ ⊕ D₂  [ Ps≈Qs ]-cong = ⊕-cong Ps≈Qs D₁ D₂
  where
  _[_]-cong′ :
    ∀ {i n Ps Qs} {C : Context ∞ n} →
    Non-degenerate′ ∞ C → (∀ x → [ i ] Ps x ≈ Qs x) →
    [ i ] C [ Ps ] ≈′ C [ Qs ]
  force (D [ Ps≈Qs ]-cong′) = force D [ Ps≈Qs ]-cong

  ⊕-cong :
    ∀ {i n Ps Qs} {C₁ C₂ : Context ∞ n} →
    (∀ x → [ i ] Ps x ≈ Qs x) →
    Non-degenerate-summand ∞ C₁ →
    Non-degenerate-summand ∞ C₂ →
    [ i ] (C₁ [ Ps ]) ⊕ (C₂ [ Ps ]) ≈ (C₁ [ Qs ]) ⊕ (C₂ [ Qs ])
  ⊕-cong {Ps = Ps} {Qs} Ps≈Qs = λ where
    (process P₁) (process P₂) →
      (context P₁ [ Ps ]) ⊕ (context P₂ [ Ps ])  ∼⟨ symmetric (SE.≡→∼ (context-[] P₁) SE.⊕-cong SE.≡→∼ (context-[] P₂)) ⟩ ≈:
      P₁ ⊕ P₂                                    ∼⟨ SE.≡→∼ (context-[] P₁) SE.⊕-cong SE.≡→∼ (context-[] P₂) ⟩■
      (context P₁ [ Qs ]) ⊕ (context P₂ [ Qs ])

    (process P₁) (action {μ = μ₂} {C = C₂} D₂) →
      (context P₁ [ Ps ]) ⊕ μ₂ · (C₂ [ Ps ]′)  ∼⟨ symmetric (SE.≡→∼ (context-[] P₁)) SE.⊕-cong (_ ■) ⟩
      P₁ ⊕ μ₂ · (C₂ [ Ps ]′)                   ∼′⟨ ⊕·-cong (D₂ [ Ps≈Qs ]-cong′) ⟩ S.∼:
      P₁ ⊕ μ₂ · (C₂ [ Qs ]′)                   ∼⟨ SE.≡→∼ (context-[] P₁) SE.⊕-cong (_ ■) ⟩■
      (context P₁ [ Qs ]) ⊕ μ₂ · (C₂ [ Qs ]′)

    (action {μ = μ₁} {C = C₁} D₁) (process P₂) →
      μ₁ · (C₁ [ Ps ]′) ⊕ (context P₂ [ Ps ])  ∼⟨ (_ ■) SE.⊕-cong symmetric (SE.≡→∼ (context-[] P₂)) ⟩
      μ₁ · (C₁ [ Ps ]′) ⊕ P₂                   ∼′⟨ ·⊕-cong (D₁ [ Ps≈Qs ]-cong′) ⟩ S.∼:
      μ₁ · (C₁ [ Qs ]′) ⊕ P₂                   ∼⟨ (_ ■) SE.⊕-cong SE.≡→∼ (context-[] P₂) ⟩■
      μ₁ · (C₁ [ Qs ]′) ⊕ (context P₂ [ Qs ])

    (action {μ = μ₁} {C = C₁} D₁) (action {μ = μ₂} {C = C₂} D₂) →
      μ₁ · (C₁ [ Ps ]′) ⊕ μ₂ · (C₂ [ Ps ]′)  ∼⟨ (D₁ [ Ps≈Qs ]-cong′) ·⊕·-cong (D₂ [ Ps≈Qs ]-cong′) ⟩■
      μ₁ · (C₁ [ Qs ]′) ⊕ μ₂ · (C₂ [ Qs ]′)

_[_]-cong′ :
  ∀ {i n Ps Qs} {C : Context ∞ n} →
  Non-degenerate ∞ C → (∀ x → [ i ] Ps x ≈′ Qs x) →
  [ i ] C [ Ps ] ≈′ C [ Qs ]
force (C [ Ps≈Qs ]-cong′) = C [ (λ x → force (Ps≈Qs x)) ]-cong

-- A variant of _[_]-cong for weakly guarded contexts.
--
-- Note that the input uses the primed variant of weak bisimilarity.
--
-- I got the idea for this lemma from Lemma 23 in Schäfer and Smolka's
-- "Tower Induction and Up-to Techniques for CCS with Fixed Points".

[]-cong-w :
  ∀ {i n Ps Qs} {C : Context ∞ n} →
  Weakly-guarded C → Non-degenerate ∞ C → (∀ x → [ i ] Ps x ≈′ Qs x) →
  [ i ] C [ Ps ] ≈ C [ Qs ]
[]-cong-w ()        hole
[]-cong-w _         ∅          Ps≈Qs = reflexive
[]-cong-w (W₁ ∣ W₂) (D₁ ∣ D₂)  Ps≈Qs = []-cong-w W₁ D₁ Ps≈Qs ∣-cong
                                       []-cong-w W₂ D₂ Ps≈Qs
[]-cong-w action    (action D) Ps≈Qs = refl ·-cong
                                         (force D [ Ps≈Qs ]-cong′)
[]-cong-w (⟨ν⟩ W)   (⟨ν⟩ D)    Ps≈Qs = ⟨ν refl ⟩-cong
                                         ([]-cong-w W D Ps≈Qs)
[]-cong-w (! W)     (! D)      Ps≈Qs = !-cong []-cong-w W D Ps≈Qs
[]-cong-w {Ps = Ps} {Qs}
          (W₁ ⊕ W₂) (D₁ ⊕ D₂)  Ps≈Qs = case D₁ ,′ D₂ of λ where
  (process P₁ , process P₂) →
    (context P₁ [ Ps ]) ⊕ (context P₂ [ Ps ])  ∼⟨ symmetric (SE.≡→∼ (context-[] P₁) SE.⊕-cong SE.≡→∼ (context-[] P₂)) ⟩ ≈:
    P₁ ⊕ P₂                                    ∼⟨ SE.≡→∼ (context-[] P₁) SE.⊕-cong SE.≡→∼ (context-[] P₂) ⟩■
    (context P₁ [ Qs ]) ⊕ (context P₂ [ Qs ])

  (process P₁ , action {μ = μ₂} {C = C₂} D₂) →
    (context P₁ [ Ps ]) ⊕ μ₂ · (C₂ [ Ps ]′)  ∼⟨ symmetric (SE.≡→∼ (context-[] P₁)) SE.⊕-cong (_ ■) ⟩
    P₁ ⊕ μ₂ · (C₂ [ Ps ]′)                   ∼′⟨ ⊕·-cong (force D₂ [ Ps≈Qs ]-cong′) ⟩ S.∼:
    P₁ ⊕ μ₂ · (C₂ [ Qs ]′)                   ∼⟨ SE.≡→∼ (context-[] P₁) SE.⊕-cong (_ ■) ⟩■
    (context P₁ [ Qs ]) ⊕ μ₂ · (C₂ [ Qs ]′)

  (action {μ = μ₁} {C = C₁} D₁ , process P₂) →
    μ₁ · (C₁ [ Ps ]′) ⊕ (context P₂ [ Ps ])  ∼⟨ (_ ■) SE.⊕-cong symmetric (SE.≡→∼ (context-[] P₂)) ⟩
    μ₁ · (C₁ [ Ps ]′) ⊕ P₂                   ∼′⟨ ·⊕-cong (force D₁ [ Ps≈Qs ]-cong′) ⟩ S.∼:
    μ₁ · (C₁ [ Qs ]′) ⊕ P₂                   ∼⟨ (_ ■) SE.⊕-cong SE.≡→∼ (context-[] P₂) ⟩■
    μ₁ · (C₁ [ Qs ]′) ⊕ (context P₂ [ Qs ])

  (action {μ = μ₁} {C = C₁} D₁ , action {μ = μ₂} {C = C₂} D₂) →
    μ₁ · (C₁ [ Ps ]′) ⊕ μ₂ · (C₂ [ Ps ]′)  ∼⟨ (force D₁ [ Ps≈Qs ]-cong′) ·⊕·-cong (force D₂ [ Ps≈Qs ]-cong′) ⟩■
    μ₁ · (C₁ [ Qs ]′) ⊕ μ₂ · (C₂ [ Qs ]′)

-- A generalisation to systems of inequations of the following
-- property: If two processes satisfy the same equation X ≳ C [ X ],
-- for a weakly guarded, non-degenerate context C, then the two
-- processes are weakly bisimilar (assuming extensionality).
--
-- This result is a variant of
-- Bisimilarity.Exercises.Coinductive.CCS.unique-solutions.
-- Proposition 4.4.4 in Milner's "Operational and Algebraic Semantics
-- of Concurrent Processes" is perhaps more useful in practice, as
-- well as some of the results in Sangiorgi's "Equations,
-- Contractions, and Unique Solutions".

module _ (ext : Proc-extensionality) where

  mutual

    unique-solutions :
      ∀ {i n} {Ps Qs : Fin n → Proc ∞} {C : Fin n → Context ∞ n} →
      (∀ x → Weakly-guarded (C x)) →
      (∀ x → Non-degenerate ∞ (C x)) →
      (∀ x → Ps x ≳ C x [ Ps ]) →
      (∀ x → Qs x ≳ C x [ Qs ]) →
      ∀ x → [ i ] Ps x ≈ Qs x
    unique-solutions {i} {Ps = Ps} {Qs} {C} w nd ≳C[Ps] ≳C[Qs] x =
      Ps x        ∼⟨ ≳C[Ps] x ⟩
      C x [ Ps ]  ∼′⟨ ≈: ⟨ lr ≳C[Ps] ≳C[Qs] , Σ-map id (Σ-map id symmetric) ∘ lr ≳C[Qs] ≳C[Ps] ⟩ ⟩ ≳:
      C x [ Qs ]  ∽⟨ ≳C[Qs] x ⟩■
      Qs x
      where
      lr :
        ∀ {Ps Qs μ P} →
        (∀ x → Ps x ≳ C x [ Ps ]) →
        (∀ x → Qs x ≳ C x [ Qs ]) →
        C x [ Ps ] [ μ ]⟶ P →
        ∃ λ Q → C x [ Qs ] [ μ ]⇒̂ Q × [ i ] P ≈′ Q
      lr {Ps} {Qs} {μ} ≳C[Ps] ≳C[Qs] ⟶P =
        case 6-2-15-nd ext (C x) (w x) (nd x) ⟶P of λ where
          (C′ , nd′ , refl , trs) →
              _
            , (C x [ Qs ]  →⟨ trs Qs ⟩■
               C′ [ Qs ])
            , (C′ [ Ps ]  ∼⟨ nd′ [ unique-solutions′ w nd ≳C[Ps] ≳C[Qs] ]-cong′ ⟩■
               C′ [ Qs ])

    unique-solutions′ :
      ∀ {i n} {Ps Qs : Fin n → Proc ∞} {C : Fin n → Context ∞ n} →
      (∀ x → Weakly-guarded (C x)) →
      (∀ x → Non-degenerate ∞ (C x)) →
      (∀ x → Ps x ≳ C x [ Ps ]) →
      (∀ x → Qs x ≳ C x [ Qs ]) →
      ∀ x → [ i ] Ps x ≈′ Qs x
    force (unique-solutions′ w nd ≳C[Ps] ≳C[Qs] x) =
      unique-solutions w nd ≳C[Ps] ≳C[Qs] x
