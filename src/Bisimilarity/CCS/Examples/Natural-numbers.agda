------------------------------------------------------------------------
-- An example that uses natural numbers as names, implemented using
-- the coinductive definition of bisimilarity
------------------------------------------------------------------------

{-# OPTIONS --safe --sized-types #-}

module Bisimilarity.CCS.Examples.Natural-numbers where

open import Equality.Propositional
open import Logical-equivalence using (_⇔_)
open import Prelude
open import Prelude.Size

open import Bijection equality-with-J using (_↔_)
open import Equality.Decision-procedures equality-with-J
open import Fin equality-with-J
open import Function-universe equality-with-J as F
  hiding (id; _∘_; Distinct↔≢)
open import Nat equality-with-J hiding (Distinct)

open import Bisimilarity.CCS
import Bisimilarity.Equational-reasoning-instances
open import Bisimilarity.CCS.Examples
open import Equational-reasoning
open import Labelled-transition-system.CCS ℕ

open import Bisimilarity CCS

module _ (μ : Action) where

  -- Two processes that are strongly bisimilar.

  P : ∀ {i} → ℕ → Proc i
  P n = Restricted n ∣ (μ · λ { .force → P (1 + n) })

  Q : ∀ {i} → Proc i
  Q = μ · λ { .force → Q }

  P∼Q : ∀ {i n} → [ i ] P n ∼ Q
  P∼Q {n = n} =
    P n    ∼⟨ Restricted∼∅ ∣-cong (refl ·-cong λ { .force → P∼Q }) ⟩
    ∅ ∣ Q  ∼⟨ ∣-left-identity ⟩■
    Q

  -- Q is not finite.

  Q-infinite : ¬ Finite Q
  Q-infinite (action f) = Q-infinite f

  -- However, Q is regular.

  Q-regular : Regular Q
  Q-regular = 1 , (λ _ → Q) , (fzero ,_) ∘ lemma
    where
    lemma : ∀ {P} → Subprocess P Q → Equal ∞ P Q
    lemma (refl eq)    = eq
    lemma (action sub) = lemma sub

  -- The processes in the family P are not finite.

  P-infinite : ∀ {n} → ¬ Finite (P n)
  P-infinite (_ ∣ action f) = P-infinite f

  -- Furthermore they are irregular.

  P-irregular : ∀ {n} → ¬ Regular (P n)
  P-irregular (k , Qs , hyp) = irregular′ k hyp
    where
    Regular′ : ℕ → ∀ k → (Fin k → Proc ∞) → Type
    Regular′ n k Qs =
      ∀ {Q} → Subprocess Q (P n) →
        ∃ λ (i : Fin k) → Equal ∞ Q (Qs i)

    irregular′ : ∀ {n} k {Qs} → ¬ Regular′ n k Qs
    irregular′ {n} zero {Qs} =
      Regular′ n zero Qs        ↝⟨ _$ refl (Proc-refl _) ⟩
      (∃ λ (i : Fin zero) → _)  ↝⟨ proj₁ ⟩□
      ⊥                         □
    irregular′ {n} (suc k) {Qs} =
      Regular′ n (suc k) Qs               ↝⟨ lemma₂ ⟩
      (∃ λ Qs′ → Regular′ (suc n) k Qs′)  ↝⟨ irregular′ k ∘ proj₂ ⟩□
      ⊥                                   □
      where
      lemma₁ :
        ∀ {Q} m {n} → Subprocess Q (P (1 + m + n)) → ¬ Equal ∞ Q (P n)
      lemma₁ m (par-right (action sub)) eq = lemma₁ (suc m) sub eq

      lemma₁ m {n} (refl (⟨ν refl ⟩ _ ∣ _)) (⟨ν suc[m+n]≡n ⟩ _ ∣ _) =
        ≢1+ _ (n            ≡⟨ sym suc[m+n]≡n ⟩
               suc (m + n)  ≡⟨ cong suc (+-comm m) ⟩∎
               suc (n + m)  ∎)

      lemma₁ _ (par-left (refl ()))                        (_ ∣ _)
      lemma₁ _ (par-left (restriction (refl ())))          (_ ∣ _)
      lemma₁ _ (par-left (restriction (action (refl ())))) (_ ∣ _)
      lemma₁ _ (par-right (refl p)) q
        with Proc-trans (Proc-sym p) q
      ... | ()

      lemma₂ : ∀ {n k Qs} →
               Regular′ n (suc k) Qs →
               ∃ λ Qs′ → Regular′ (suc n) k Qs′
      lemma₂ {n} {k} {Qs} reg =
        let i , Pn≡Qsi = reg (refl (Proc-refl _))
            Fin↔       = Fin↔Fin+≢ i
            Qs′        =
              Fin k                                   ↔⟨ Fin↔ ⟩
              (∃ λ (j : Fin (suc k)) → Distinct j i)  ↝⟨ Qs ∘ proj₁ ⟩□
              Proc ∞                                  □
        in
        Qs′ , λ {Q} →
          Subprocess Q (P (1 + n))                                    ↝⟨ (λ sub → reg (par-right (action sub)) , lemma₁ 0 sub) ⟩

          (∃ λ (j : Fin (suc k)) → Equal ∞ Q (Qs j)) ×
          ¬ Equal ∞ Q (P n)                                           ↝⟨ (λ { ((j , Q≡Qsj) , Q≢Pn) →
                                                                                ( j
                                                                                , (case j Fin.≟ i of λ where
                                                                                     (inj₁ refl) → ⊥-elim $
                                                                                                     Q≢Pn (Proc-trans Q≡Qsj (Proc-sym Pn≡Qsi))
                                                                                     (inj₂ j≢i)  → _⇔_.from (Distinct↔≢ _) j≢i)
                                                                                )
                                                                              , Q≡Qsj }) ⟩
          (∃ λ (j : ∃ λ (j : Fin (suc k)) → Distinct j i) →
             Equal ∞ Q (Qs (proj₁ j)))                                ↝⟨ ∃-cong (λ _ → ≡⇒↝ _ $ cong (λ j → Equal ∞ Q (Qs (proj₁ j))) $ sym $
                                                                         _↔_.right-inverse-of Fin↔ _) ⟩
          (∃ λ (j : ∃ λ (j : Fin (suc k)) → Distinct j i) →
             Equal ∞ Q (Qs (proj₁ (_↔_.to Fin↔ (_↔_.from Fin↔ j)))))  ↔⟨⟩

          (∃ λ (j : ∃ λ (j : Fin (suc k)) → Distinct j i) →
             Equal ∞ Q (Qs′ (_↔_.from Fin↔ j)))                       ↝⟨ Σ-cong (inverse Fin↔) (λ _ → F.id) ⟩□

          (∃ λ (j : Fin k) → Equal ∞ Q (Qs′ j))                       □
