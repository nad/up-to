------------------------------------------------------------------------
-- An up-to technique for CCS
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Bisimilarity.Up-to.CCS {ℓ} {Name : Set ℓ} where

open import Equality.Propositional
open import Logical-equivalence using (_⇔_)
open import Prelude

open import Bijection equality-with-J using (_↔_)
open import Function-universe equality-with-J hiding (id; _∘_)

import Bisimilarity.Coinductive.Equational-reasoning-instances
open import Bisimilarity.Exercises.Coinductive.CCS
  using (_[_]-cong; 6-1-3-2; ≡→∼)
open import Equational-reasoning
open import Indexed-container
open import Labelled-transition-system.CCS Name
open import Relation

open import Bisimilarity.Coinductive CCS
open import Bisimilarity.Exercises.Coinductive.CCS
open import Bisimilarity.Step CCS _[_]⟶_ using (Step; Step↔S̲t̲e̲p̲)
open import Bisimilarity.Up-to CCS

-- Up to context for a very simple kind of context.

Up-to-!-context : Trans₂ ℓ (Proc ∞)
Up-to-!-context R (P , Q) =
  ∃ λ P′ → ∃ λ Q′ → P ≡ ! P′ × R (P′ , Q′) × ! Q′ ≡ Q

-- This transformer is size-preserving.

Up-to-!-context-size-preserving : Size-preserving Up-to-!-context
Up-to-!-context-size-preserving
  {R = R} {i = i} R⊆∼ (P′ , Q′ , refl , P′RQ′ , refl) =

                     $⟨ P′RQ′ ⟩
  R (P′ , Q′)        ↝⟨ R⊆∼ ⟩
  [ i ] P′ ∼ Q′      ↝⟨ !-cong_ ⟩□
  [ i ] ! P′ ∼ ! Q′  □

-- Up to context for CCS (for polyadic contexts).

Up-to-context : Trans₂ ℓ (Proc ∞)
Up-to-context R (p , q) =
  ∃ λ n →
  ∃ λ (C : Context ∞ n) →
  ∃ λ ps →
  ∃ λ qs →
  Equal ∞ p (C [ ps ])
    ×
  Equal ∞ q (C [ qs ])
    ×
  ∀ x → R (ps x , qs x)

-- Up to context is monotone.

Up-to-context-monotone : Monotone Up-to-context
Up-to-context-monotone R⊆S =
  Σ-map id $ Σ-map id $ Σ-map id $ Σ-map id $ Σ-map id $ Σ-map id
    (R⊆S ∘_)

-- Up to context is size-preserving.

Up-to-context-size-preserving : Size-preserving Up-to-context
Up-to-context-size-preserving =
  _⇔_.from (monotone→⇔ Up-to-context-monotone)
  (λ where
     {x = p , q} (_ , C , ps , qs , eq₁ , eq₂ , ps∼qs) →

       p         ∼⟨ ≡→∼ eq₁ ⟩
       C [ ps ]  ∼⟨ C [ ps∼qs ]-cong ⟩
       C [ qs ]  ∼⟨ symmetric (≡→∼ eq₂) ⟩■
       q)

-- Note that up to context is not compatible (assuming that Name is
-- inhabited).
--
-- This counterexample is a minor variant of one due to Pous and
-- Sangiorgi, who state that up to context would have been compatible
-- if the Step function had been defined in a slightly different way
-- (see Remark 6.4.2 in "Enhancements of the bisimulation proof
-- method").

¬-Up-to-context-compatible : Name → ¬ Compatible Up-to-context
¬-Up-to-context-compatible x comp = contradiction
  where
  a = x , true
  b = x , false
  c = a
  d = a

  a≢b : ¬ a ≡ b
  a≢b ()

  data R : Rel₂ ℓ (Proc ∞) where
    base : R (! name a · (b ·) , ! name a · (c ·))

  data S₀ : Rel₂ ℓ (Proc ∞) where
    base : S₀ (! name a · (b ·) ∣ b · , ! name a · (c ·) ∣ c ·)

  S : Rel₂ ℓ (Proc ∞)
  S = Up-to-bisimilarity S₀

  d!ab[R]d!ac : Up-to-context R ( name d · (! name a · (b ·))
                                , name d · (! name a · (c ·))
                                )
  d!ab[R]d!ac =
      1
    , name d ·′ (λ { .force → hole fzero })
    , (λ _ → ! name a · (b ·))
    , (λ _ → ! name a · (c ·))
    , refl ·′ (λ { .force → Proc-refl _ })
    , refl ·′ (λ { .force → Proc-refl _ })
    , (λ _ → base)

  ¬!ab[S]!ac : ¬ Up-to-context S (! name a · (b ·) , ! name a · (c ·))
  ¬!ab[S]!ac (n , C , Ps , Qs , !ab≡C[Ps] , !ac≡C[Qs] , PsSQs) =

                                    $⟨ Matches-[] C ⟩
    Matches ∞ (C [ Ps ]) C          ↝⟨ Matches-cong (Proc-sym !ab≡C[Ps]) ⟩
    Matches ∞ (! name a · (b ·)) C  ↝⟨ helper !ab≡C[Ps] !ac≡C[Qs] ⟩□
    ⊥                               □

    where

    helper : Equal ∞ (! name a · (b ·)) (C [ Ps ]) →
             Equal ∞ (! name a · (c ·)) (C [ Qs ]) →
             ¬ Matches ∞ (! name a · (b ·)) C

    helper !ab≡ _ (hole x) = case PsSQs x of λ where
      (_ , Ps[x]∼!ab∣b , _ , base , _) →
                                                    $⟨ Ps[x]∼!ab∣b ⟩
        Ps x ∼ ! name a · (b ·) ∣ b ·               ↝⟨ transitive {a = ℓ} (≡→∼ !ab≡) ⟩
        ! name a · (b ·) ∼ ! name a · (b ·) ∣ b ·   ↝⟨ (λ !ab∼!ab∣b → Σ-map id proj₁ $ S̲t̲e̲p̲.right-to-left !ab∼!ab∣b (par-right action)) ⟩
        (∃ λ P′ → ! name a · (b ·) [ name b ]⟶ P′)  ↝⟨ cancel-name ∘ !-only ·′-only ∘ proj₂ ⟩
        a ≡ b                                       ↝⟨ a≢b ⟩□
        ⊥                                           □

    helper (! ab≡) (! ac≡) (! hole x) = case PsSQs x of λ where
      (_ , Ps[x]∼!ab∣b , _ , base , _) →
                                                  $⟨ Ps[x]∼!ab∣b ⟩
        Ps x ∼ ! name a · (b ·) ∣ b ·             ↝⟨ transitive {a = ℓ} (≡→∼ ab≡) ⟩
        name a · (b ·) ∼ ! name a · (b ·) ∣ b ·   ↝⟨ (λ ab∼!ab∣b → Σ-map id proj₁ $ S̲t̲e̲p̲.right-to-left ab∼!ab∣b (par-right action)) ⟩
        (∃ λ P′ → name a · (b ·) [ name b ]⟶ P′)  ↝⟨ cancel-name ∘ ·′-only ∘ proj₂ ⟩
        a ≡ b                                     ↝⟨ a≢b ⟩□
        ⊥                                         □

    helper (! (_ ·′ b≡′)) (! (_ ·′ c≡′)) (! action {C = C} M) =
      case force C , force b≡′ , force c≡′ , force M {j = ∞} ⦂
             (∃ λ C → Equal ∞ _ (C [ Ps ]) ×
                      Equal ∞ _ (C [ Qs ]) × Matches ∞ _ C) of λ where

        (._ , b≡ , _ , hole x) → case PsSQs x of λ where
          (_ , Ps[x]∼!ab∣b , _ , base , _) →
                                           $⟨ Ps[x]∼!ab∣b ⟩
            Ps x ∼ ! name a · (b ·) ∣ b ·  ↝⟨ transitive {a = ℓ} (≡→∼ b≡) ⟩
            b · ∼ ! name a · (b ·) ∣ b ·   ↝⟨ (λ b∼!ab∣b → Σ-map id proj₁ $
                                                             S̲t̲e̲p̲.right-to-left b∼!ab∣b (par-left (replication (par-right action)))) ⟩
            (∃ λ P′ → b · [ name a ]⟶ P′)  ↝⟨ cancel-name ∘ ·′-only ∘ proj₂ ⟩
            b ≡ a                          ↝⟨ a≢b ∘ sym ⟩□
            ⊥                              □

        (._ , _ , c≡b ·′ _ , action _) →
                           $⟨ c≡b ⟩
          name c ≡ name b  ↝⟨ cancel-name ⟩
          c ≡ b            ↝⟨ a≢b ⟩□
          ⊥                □

  R⊆StepS : R ⊆ ⟦ S̲t̲e̲p̲ ⟧ S
  R⊆StepS base = S̲t̲e̲p̲.⟨ lr , rl ⟩
    where
    lr : ∀ {P′ μ} →
         ! name a · (b ·) [ μ ]⟶ P′ →
         ∃ λ Q′ → ! name a · (c ·) [ μ ]⟶ Q′ × S (P′ , Q′)
    lr {P′} {μ} !ab[μ]⟶P′ = case 6-1-3-2 !ab[μ]⟶P′ of λ where
      (inj₁ (.(b ·) , action , P′∼!ab∣b)) →
          ! name a · (c ·) ∣ c ·
        , replication (par-right action)
        , _
        , (P′                      ∼⟨ P′∼!ab∣b ⟩■
           ! name a · (b ·) ∣ b ·)
        , _
        , base
        , (! name a · (c ·) ∣ c ·  ■)

      (inj₂ (μ≡τ , _)) → ⊥-elim $ name≢τ (
        name a  ≡⟨ !-only ·′-only !ab[μ]⟶P′ ⟩
        μ       ≡⟨ μ≡τ ⟩∎
        τ       ∎)

    rl : ∀ {Q′ μ} →
         ! name a · (c ·) [ μ ]⟶ Q′ →
         ∃ λ P′ → ! name a · (b ·) [ μ ]⟶ P′ × S (P′ , Q′)
    rl {Q′} {μ} !ac[μ]⟶Q′ = case 6-1-3-2 !ac[μ]⟶Q′ of λ where
      (inj₁ (.(c ·) , action , Q′∼!ac∣c)) →
          ! name a · (b ·) ∣ b ·
        , replication (par-right action)
        , _
        , (! name a · (b ·) ∣ b ·  ■)
        , _
        , base
        , (! name a · (c ·) ∣ c ·  ∼⟨ symmetric Q′∼!ac∣c ⟩■
           Q′)

      (inj₂ (μ≡τ , _)) → ⊥-elim $ name≢τ (
        name a  ≡⟨ !-only ·′-only !ac[μ]⟶Q′ ⟩
        μ       ≡⟨ μ≡τ ⟩∎
        τ       ∎)

  -- Note the use of compatibility in [R]⊆Step[S].

  [R]⊆Step[S] : Up-to-context R ⊆ ⟦ S̲t̲e̲p̲ ⟧ (Up-to-context S)
  [R]⊆Step[S] =
    Up-to-context R             ⊆⟨ Up-to-context-monotone (λ {x} → R⊆StepS {x}) ⟩
    Up-to-context (⟦ S̲t̲e̲p̲ ⟧ S)  ⊆⟨ comp _ ⟩∎
    ⟦ S̲t̲e̲p̲ ⟧ (Up-to-context S)  ∎

  contradiction : ⊥
  contradiction =
                                                              $⟨ d!ab[R]d!ac ⟩
    Up-to-context R ( name d · (! name a · (b ·))
                    , name d · (! name a · (c ·))
                    )                                         ↝⟨ [R]⊆Step[S] ⟩

    ⟦ S̲t̲e̲p̲ ⟧ (Up-to-context S) ( name d · (! name a · (b ·))
                               , name d · (! name a · (c ·))
                               )                              ↝⟨ (λ s → S̲t̲e̲p̲.left-to-right s action) ⟩

    (∃ λ P → name d · (! name a · (c ·)) [ name d ]⟶ P ×
             Up-to-context S (! name a · (b ·) , P))          ↝⟨ (λ { (P , d!ac[d]⟶P  , !ab[S]P) →
                                                                      subst (Up-to-context S ∘ (_ ,_)) (·′-only⟶ d!ac[d]⟶P) !ab[S]P }) ⟩

    Up-to-context S (! name a · (b ·) , ! name a · (c ·))     ↝⟨ ¬!ab[S]!ac ⟩□

    ⊥                                                         □
