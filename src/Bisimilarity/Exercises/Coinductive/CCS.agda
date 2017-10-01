------------------------------------------------------------------------
-- Some exercises and results related to CCS, mostly from
-- "Enhancements of the bisimulation proof method" by Pous and
-- Sangiorgi
--
-- Implemented using the coinductive definition of bisimilarity.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Bisimilarity.Exercises.Coinductive.CCS {ℓ} {Name : Set ℓ} where

open import Equality.Propositional
open import Prelude

import Bisimilarity.Coinductive.Equational-reasoning-instances
import Bisimilarity.Exercises.Other.CCS
open import Equational-reasoning
open import Labelled-transition-system.CCS Name

open import Bisimilarity.Coinductive CCS
import Labelled-transition-system.Equational-reasoning-instances CCS

------------------------------------------------------------------------
-- Congruence lemmas

-- Some lemmas used to prove the congruence results below as well as
-- similar results in Similarity.Strong.CCS.

module Cong-lemmas
  ({R} R′ : Proc ∞ → Proc ∞ → Set ℓ)
  ⦃ _ : Convertible R R′ ⦄
  ⦃ _ : Convertible R′ R′ ⦄
  ⦃ _ : Convertible _∼_ R′ ⦄
  ⦃ _ : Transitive R′ R′ ⦄
  (left-to-right :
   ∀ {P Q} → R P Q →
   ∀ {P′ μ} → P [ μ ]⟶ P′ → ∃ λ Q′ → Q [ μ ]⟶ Q′ × R′ P′ Q′)
  where

  private

    infix -2 R′:_

    R′:_ : ∀ {P Q} → R′ P Q → R′ P Q
    R′:_ = id

    infix -3 lr-result

    lr-result :
      ∀ {P′ Q Q′} μ → R′ P′ Q′ → Q [ μ ]⟶ Q′ →
      ∃ λ Q′ → Q [ μ ]⟶ Q′ × R′ P′ Q′
    lr-result _ P′∼′Q′ Q⟶Q′ = _ , Q⟶Q′ , P′∼′Q′

    syntax lr-result μ P′∼′Q′ Q⟶Q′ = P′∼′Q′ [ μ ]⟵ Q⟶Q′

  ∣-cong :
    (∀ {P P′ Q Q′} → R′ P P′ → R′ Q Q′ → R′ (P ∣ Q) (P′ ∣ Q′)) →
    ∀ {P₁ P₂ Q₁ Q₂ S₁ μ} →
    R P₁ P₂ → R Q₁ Q₂ → P₁ ∣ Q₁ [ μ ]⟶ S₁ →
    ∃ λ S₂ → P₂ ∣ Q₂ [ μ ]⟶ S₂ × R′ S₁ S₂
  ∣-cong _∣-cong′_ P₁∼P₂ Q₁∼Q₂ = λ where
    (par-left  tr)  → Σ-map (_∣ _)
                        (Σ-map par-left
                               (_∣-cong′ convert Q₁∼Q₂))
                        (left-to-right P₁∼P₂ tr)
    (par-right tr)  → Σ-map (_ ∣_)
                        (Σ-map par-right
                               (convert P₁∼P₂ ∣-cong′_))
                        (left-to-right Q₁∼Q₂ tr)
    (par-τ tr₁ tr₂) → Σ-zip _∣_ (Σ-zip par-τ _∣-cong′_)
                        (left-to-right P₁∼P₂ tr₁)
                        (left-to-right Q₁∼Q₂ tr₂)

  ⊕-cong :
    ∀ {P₁ P₁′ P₂ P₂′ S μ} →
    R P₁ P₁′ → R P₂ P₂′ → P₁ ⊕ P₂ [ μ ]⟶ S →
    ∃ λ S′ → P₁′ ⊕ P₂′ [ μ ]⟶ S′ × R′ S S′
  ⊕-cong {P₁} {P₁′} {P₂} {P₂′} {S} {μ} P₁∼P₁′ P₂∼P₂′ = λ where
    (choice-left P₁⟶S) → case left-to-right P₁∼P₁′ P₁⟶S of λ where
      (S′ , P₁′⟶S′ , S∼′S′) →
        S          ∼⟨ S∼′S′ ⟩■
        S′
          [ μ ]⟵   ←⟨ choice-left P₁′⟶S′ ⟩■
        P₁′ ⊕ P₂′

    (choice-right P₂⟶S) → case left-to-right P₂∼P₂′ P₂⟶S of λ where
      (S′ , P₂′⟶S′ , S∼′S′) →
        S          ∼⟨ S∼′S′ ⟩■
        S′
          [ μ ]⟵   ←⟨ choice-right P₂′⟶S′ ⟩■
        P₁′ ⊕ P₂′

  ·′-cong :
    ∀ {P₁ P₂ Q₁ μ μ′} →
    R′ (force P₁) (force P₂) → μ ·′ P₁ [ μ′ ]⟶ Q₁ →
    ∃ λ Q₂ → μ ·′ P₂ [ μ′ ]⟶ Q₂ × R′ Q₁ Q₂
  ·′-cong {P₁} {P₂} {μ = μ} P₁∼P₂ action =
    force P₁  ∼⟨ P₁∼P₂ ⟩■
    force P₂
      [ μ ]⟵  ←⟨ _[_]⟶_.action ⟩■
    μ ·′ P₂

  ⟨ν⟩-cong :
    (∀ {a P P′} → R′ P P′ → R′ (⟨ν a ⟩ P) (⟨ν a ⟩ P′)) →
    ∀ {a μ P P′ Q} →
    R P P′ → ⟨ν a ⟩ P [ μ ]⟶ Q →
    ∃ λ Q′ → ⟨ν a ⟩ P′ [ μ ]⟶ Q′ × R′ Q Q′
  ⟨ν⟩-cong ⟨ν⟩-cong′ {a} {μ} {P′ = P′} P∼P′
           (restriction {P′ = Q} a∉μ P⟶Q) =
    case left-to-right P∼P′ P⟶Q of λ where
      (Q′ , P′⟶Q′ , Q∼′Q′) →
        ⟨ν a ⟩ Q   ∼⟨ ⟨ν⟩-cong′ Q∼′Q′ ⟩■
        ⟨ν a ⟩ Q′
          [ μ ]⟵   ←⟨ restriction a∉μ P′⟶Q′ ⟩■
        ⟨ν a ⟩ P′

  !-cong :
    (∀ {μ P P₀} →
     ! P [ μ ]⟶ P₀ →
     (∃ λ P′ → P [ μ ]⟶ P′ × P₀ ∼ ! P ∣ P′)
       ⊎
     (μ ≡ τ × ∃ λ P′ → ∃ λ P″ → ∃ λ a →
      P [ name a ]⟶ P′ × P [ name (co a) ]⟶ P″ ×
      P₀ ∼ (! P ∣ P′) ∣ P″)) →
    (∀ {P P′ Q Q′} → R′ P P′ → R′ Q Q′ → R′ (P ∣ Q) (P′ ∣ Q′)) →
    (∀ {P P′} → R′ P P′ → R′ (! P) (! P′)) →
    ∀ {P P′ Q μ} →
    R P P′ → ! P [ μ ]⟶ Q →
    ∃ λ Q′ → ! P′ [ μ ]⟶ Q′ × R′ Q Q′
  !-cong 6-1-3-2 _∣-cong′_ !-cong′_ {P} {P′} {Q} {μ} P∼P′ !P⟶Q =
    case 6-1-3-2 !P⟶Q of λ where

      (inj₁ (P″ , P⟶P″ , Q∼!P∣P″)) →
        let Q′ , P′⟶Q′ , P″∼′Q′ = left-to-right P∼P′ P⟶P″
        in
        Q          ∼⟨ R′: convert Q∼!P∣P″ ⟩
        ! P  ∣ P″  ∼⟨ (!-cong′ convert P∼P′) ∣-cong′ P″∼′Q′ ⟩■
        ! P′ ∣ Q′
          [ μ ]⟵   ←⟨ replication (par-right P′⟶Q′) ⟩■
        ! P′

      (inj₂ (refl , P″ , P‴ , a , P⟶P″ , P⟶P‴ , Q∼!P∣P″∣P‴)) →
        let Q′ , P′⟶Q′ , P″∼′Q′ = left-to-right P∼P′ P⟶P″
            Q″ , P′⟶Q″ , P‴∼′Q″ = left-to-right P∼P′ P⟶P‴
        in
        Q                 ∼⟨ R′: convert Q∼!P∣P″∣P‴ ⟩
        (! P ∣ P″) ∣ P‴   ∼⟨ ((!-cong′ convert P∼P′) ∣-cong′ P″∼′Q′) ∣-cong′ P‴∼′Q″ ⟩■
        (! P′ ∣ Q′) ∣ Q″
          [ τ ]⟵          ←⟨ replication (par-τ (replication (par-right P′⟶Q′)) P′⟶Q″) ⟩■
        ! P′

private
  module CL {i} = Cong-lemmas [ i ]_∼′_ left-to-right

------------------------------------------------------------------------
-- Various lemmas related to _∣_

mutual

  -- _∣_ is commutative.

  ∣-comm : ∀ {P Q i} → [ i ] P ∣ Q ∼ Q ∣ P
  ∣-comm {i = i} = ⟨ lr , Σ-map id (Σ-map id symmetric) ∘ lr ⟩
    where
    lr : ∀ {P P′ Q μ} →
         P ∣ Q [ μ ]⟶ P′ →
         ∃ λ Q′ → Q ∣ P [ μ ]⟶ Q′ × [ i ] P′ ∼′ Q′
    lr (par-left tr)   = _ , par-right tr , ∣-comm′
    lr (par-right tr)  = _ , par-left tr , ∣-comm′
    lr (par-τ tr₁ tr₂) =
        _
      , par-τ tr₂ (subst (λ a → _ [ name a ]⟶ _)
                         (sym $ co-involutive _)
                         tr₁)
      , ∣-comm′

  ∣-comm′ : ∀ {P Q i} → [ i ] P ∣ Q ∼′ Q ∣ P
  force ∣-comm′ = ∣-comm

mutual

  -- _∣_ is associative.

  ∣-assoc : ∀ {P Q R i} → [ i ] P ∣ (Q ∣ R) ∼ (P ∣ Q) ∣ R
  ∣-assoc {i = i} = ⟨ lr , rl ⟩
    where
    lr : ∀ {P Q R P′ μ} →
         P ∣ (Q ∣ R) [ μ ]⟶ P′ →
         ∃ λ Q′ → (P ∣ Q) ∣ R [ μ ]⟶ Q′ × [ i ] P′ ∼′ Q′
    lr (par-left tr)               = _ , par-left (par-left tr)    , ∣-assoc′
    lr (par-right (par-left tr))   = _ , par-left (par-right tr)   , ∣-assoc′
    lr (par-right (par-right tr))  = _ , par-right tr              , ∣-assoc′
    lr (par-right (par-τ tr₁ tr₂)) = _ , par-τ (par-right tr₁) tr₂ , ∣-assoc′
    lr (par-τ tr₁ (par-left tr₂))  = _ , par-left (par-τ tr₁ tr₂)  , ∣-assoc′
    lr (par-τ tr₁ (par-right tr₂)) = _ , par-τ (par-left tr₁) tr₂  , ∣-assoc′

    rl : ∀ {P Q R Q′ μ} →
         (P ∣ Q) ∣ R [ μ ]⟶ Q′ →
         ∃ λ P′ → P ∣ (Q ∣ R) [ μ ]⟶ P′ × [ i ] P′ ∼′ Q′
    rl (par-left (par-left tr))    = _ , par-left tr               , ∣-assoc′
    rl (par-left (par-right tr))   = _ , par-right (par-left tr)   , ∣-assoc′
    rl (par-left (par-τ tr₁ tr₂))  = _ , par-τ tr₁ (par-left tr₂)  , ∣-assoc′
    rl (par-right tr)              = _ , par-right (par-right tr)  , ∣-assoc′
    rl (par-τ (par-left tr₁) tr₂)  = _ , par-τ tr₁ (par-right tr₂) , ∣-assoc′
    rl (par-τ (par-right tr₁) tr₂) = _ , par-right (par-τ tr₁ tr₂) , ∣-assoc′

  ∣-assoc′ : ∀ {P Q R i} → [ i ] P ∣ (Q ∣ R) ∼′ (P ∣ Q) ∣ R
  force ∣-assoc′ = ∣-assoc

mutual

  -- ∅ is a left identity of _∣_.

  ∣-left-identity : ∀ {P i} → [ i ] ∅ ∣ P ∼ P
  ∣-left-identity {i = i} = ⟨ lr , rl ⟩
    where

    lr : ∀ {P P′ μ} →
         ∅ ∣ P [ μ ]⟶ P′ →
         ∃ λ Q′ → P [ μ ]⟶ Q′ × [ i ] P′ ∼′ Q′
    lr (par-right tr) = _ , tr , ∣-left-identity′
    lr (par-left ())
    lr (par-τ () _)

    rl : ∀ {P Q′ μ} →
         P [ μ ]⟶ Q′ →
         ∃ λ P′ → ∅ ∣ P [ μ ]⟶ P′ × [ i ] P′ ∼′ Q′
    rl tr = _ , par-right tr , ∣-left-identity′

  ∣-left-identity′ : ∀ {P i} → [ i ] ∅ ∣ P ∼′ P
  force ∣-left-identity′ = ∣-left-identity

-- ∅ is a right identity of _∣_.

∣-right-identity : ∀ {P} → P ∣ ∅ ∼ P
∣-right-identity {P} =
  P ∣ ∅  ∼⟨ ∣-comm ⟩ ∼:
  ∅ ∣ P  ∼⟨ ∣-left-identity ⟩■
  P

mutual

  -- _∣_ preserves bisimilarity.

  infix 6 _∣-cong_ _∣-cong′_

  _∣-cong_ : ∀ {i P P′ Q Q′} →
             [ i ] P ∼ P′ → [ i ] Q ∼ Q′ → [ i ] P ∣ Q ∼ P′ ∣ Q′
  P∼P′ ∣-cong Q∼Q′ =
    ⟨ lr P∼P′ Q∼Q′
    , Σ-map id (Σ-map id symmetric) ∘
      lr (symmetric P∼P′) (symmetric Q∼Q′)
    ⟩
    where
    lr = CL.∣-cong _∣-cong′_

  _∣-cong′_ : ∀ {i P P′ Q Q′} →
              [ i ] P ∼′ P′ → [ i ] Q ∼′ Q′ → [ i ] P ∣ Q ∼′ P′ ∣ Q′
  force (P∼P′ ∣-cong′ Q∼Q′) = force P∼P′ ∣-cong force Q∼Q′

------------------------------------------------------------------------
-- Exercise 6.1.2

private

  -- A compact proof.

  6-1-2-compact : ∀ {P i} → [ i ] ! P ∣ P ∼ ! P
  6-1-2-compact =
    ⟨ (λ tr → _ , replication tr , reflexive)
    , (λ { (replication tr) → _ , tr , reflexive })
    ⟩

-- A less compact proof.

6-1-2 : ∀ {P i} → [ i ] ! P ∣ P ∼ ! P
6-1-2 {P} =
  ⟨ (λ {P′} {μ} tr →
       P′   ∼⟨ ∼′: reflexive ⟩■
       P′   [ μ ]⟵⟨ replication tr ⟩
       ! P)
  , (λ { {q′ = P′} {μ = μ} (replication tr) →
         ! P ∣ P  [ μ ]⟶⟨ tr ⟩ʳˡ
         P′       ∼⟨ ∼′: reflexive ⟩■
         P′ })
  ⟩

------------------------------------------------------------------------
-- Exercise 6.1.3 (2), plus some rearrangement lemmas

private
  module 6-1-3-2 = Bisimilarity.Exercises.Other.CCS.6-1-3-2 (record
    { _∼_       = _∼_
    ; step-∼    = step-∼
    ; finally-∼ = Equational-reasoning.finally₂
    ; reflexive = reflexive
    ; symmetric = symmetric
    ; ∣-comm    = ∣-comm
    ; ∣-assoc   = ∣-assoc
    ; _∣-cong_  = _∣-cong_
    ; 6-1-2     = 6-1-2
    })

6-1-3-2 :
  ∀ {μ P P₀} →
  ! P [ μ ]⟶ P₀ →
  (∃ λ P′ → P [ μ ]⟶ P′ × P₀ ∼ ! P ∣ P′)
    ⊎
  (μ ≡ τ × ∃ λ P′ → ∃ λ P″ → ∃ λ a →
   P [ name a ]⟶ P′ × P [ name (co a) ]⟶ P″ × P₀ ∼ (! P ∣ P′) ∣ P″)
6-1-3-2 = 6-1-3-2.6-1-3-2

swap-rightmost : ∀ {P Q R} → (P ∣ Q) ∣ R ∼ (P ∣ R) ∣ Q
swap-rightmost = 6-1-3-2.swap-rightmost

swap-in-the-middle : ∀ {P Q R S} →
                     (P ∣ Q) ∣ (R ∣ S) ∼ (P ∣ R) ∣ (Q ∣ S)
swap-in-the-middle {P} {Q} {R} {S} =
  (P ∣ Q) ∣ (R ∣ S)  ∼⟨ swap-rightmost ⟩
  (P ∣ (R ∣ S)) ∣ Q  ∼⟨ ∣-assoc ∣-cong reflexive ⟩
  ((P ∣ R) ∣ S) ∣ Q  ∼⟨ symmetric ∣-assoc ⟩ ∼:
  (P ∣ R) ∣ (S ∣ Q)  ∼⟨ reflexive ∣-cong ∣-comm ⟩■
  (P ∣ R) ∣ (Q ∣ S)

------------------------------------------------------------------------
-- A result mentioned in "Enhancements of the bisimulation proof
-- method"

mutual

  -- For a more general result, see 6-2-14 below.

  !·⊕·∼!·∣!· : ∀ {i a b} → [ i ] ! (a · ⊕ b ·) ∼ ! a · ∣ ! b ·
  !·⊕·∼!·∣!· {i} = ⟨ lr , rl ⟩
    where
    lemma = λ {a b} → ∼′:
      ! (a · ⊕ b ·) ∣ ∅  ∼⟨ ∣-right-identity ⟩ ∼′:
      ! (a · ⊕ b ·)      ∼⟨ !·⊕·∼′!·∣!· {i = i} ⟩■
      ! a · ∣ ! b ·

    left-lemma = λ {a b} → ∼′:
      ! (a · ⊕ b ·) ∣ ∅    ∼⟨ lemma ⟩ ∼′:
      ! a · ∣ ! b ·        ∼⟨ symmetric ∣-right-identity ∣-cong reflexive ⟩■
      (! a · ∣ ∅) ∣ ! b ·

    right-lemma = λ {a b} → ∼′:
      ! (a · ⊕ b ·) ∣ ∅    ∼⟨ lemma ⟩ ∼′:
      ! a · ∣  ! b ·       ∼⟨ reflexive ∣-cong symmetric ∣-right-identity ⟩■
      ! a · ∣ (! b · ∣ ∅)

    τ-lemma = λ {a b} → ∼′:
      (! (a · ⊕ b ·) ∣ ∅) ∣ ∅    ∼⟨ ∣-right-identity ⟩
      ! (a · ⊕ b ·) ∣ ∅          ∼⟨ lemma ⟩ ∼′:
      ! a · ∣ ! b ·              ∼⟨ symmetric (∣-right-identity ∣-cong ∣-right-identity) ⟩■
      (! a · ∣ ∅) ∣ (! b · ∣ ∅)

    lr : ∀ {a b P μ} →
         ! (a · ⊕ b ·) [ μ ]⟶ P →
         ∃ λ Q → ! a · ∣ ! b · [ μ ]⟶ Q × [ i ] P ∼′ Q
    lr {a} {b} {P} tr = case 6-1-3-2 tr of λ where

      (inj₁ (.∅ , choice-left action , P∼![a⊕b]∣∅)) →
        P                    ∼⟨ P∼![a⊕b]∣∅ ⟩ ∼′:
        ! (a · ⊕ b ·) ∣ ∅    ∼⟨ left-lemma ⟩■
        (! a · ∣ ∅) ∣ ! b ·  [ name a ]⟵⟨ par-left (replication (par-right action)) ⟩
        ! a ·       ∣ ! b ·

      (inj₁ (.∅ , choice-right action , P∼![a⊕b]∣∅)) →
        P                    ∼⟨ P∼![a⊕b]∣∅ ⟩ ∼′:
        ! (a · ⊕ b ·) ∣ ∅    ∼⟨ right-lemma ⟩■
        ! a · ∣ (! b · ∣ ∅)  [ name b ]⟵⟨ par-right (replication (par-right action)) ⟩
        ! a · ∣ ! b ·

      (inj₂ (refl , P′ , P″ , c , a⊕b⟶P′ , a⊕b⟶P″ , P∼![a⊕b]∣P′∣P″)) →
        let b≡co-a , P′≡∅ , P″≡∅ = Σ-map id [ id , id ]
                                     (·′⊕·′-co a⊕b⟶P′ a⊕b⟶P″) in

        P                          ∼⟨ P∼![a⊕b]∣P′∣P″ ⟩
        (! (a · ⊕ b ·) ∣ P′) ∣ P″  ∼⟨ (reflexive ∣-cong ≡⇒∼ P′≡∅) ∣-cong ≡⇒∼ P″≡∅ ⟩ ∼′:
        (! (a · ⊕ b ·) ∣ ∅) ∣ ∅    ∼⟨ τ-lemma ⟩■
        (! a · ∣ ∅) ∣ (! b · ∣ ∅)  [ τ ]⟵⟨ par-τ′ b≡co-a (replication (par-right action))
                                                         (replication (par-right action)) ⟩
        ! a · ∣ ! b ·

    rl : ∀ {a b Q μ} →
         ! a · ∣ ! b · [ μ ]⟶ Q →
         ∃ λ P → ! (a · ⊕ b ·) [ μ ]⟶ P × [ i ] P ∼′ Q
    rl {a} {b} (par-left {P′ = P′} tr) =
      case 6-1-3-2 tr of λ where

        (inj₁ (.∅ , action , P′∼!a∣∅)) →
          ! (a · ⊕ b ·)        [ name a ]⟶⟨ replication (par-right (choice-left action)) ⟩ʳˡ
          ! (a · ⊕ b ·) ∣ ∅    ∼⟨ left-lemma ⟩ ∼′:
          (! a · ∣ ∅) ∣ ! b ·  ∼⟨ symmetric P′∼!a∣∅ ∣-cong reflexive ⟩■
          P′ ∣ ! b ·

        (inj₂ (refl , .∅ , P″ , .a , action , a⟶P″ , P′∼!a∣∅∣P″)) →
          ⊥-elim (names-are-not-inverted a⟶P″)

    rl {a} {b} (par-right {Q′ = Q′} tr) =
      case 6-1-3-2 tr of λ where

        (inj₁ (.∅ , action , Q′∼!b∣∅)) →
          ! (a · ⊕ b ·)        [ name b ]⟶⟨ replication (par-right (choice-right action)) ⟩ʳˡ
          ! (a · ⊕ b ·) ∣ ∅    ∼⟨ right-lemma ⟩ ∼′:
          ! a · ∣ (! b · ∣ ∅)  ∼⟨ reflexive ∣-cong symmetric Q′∼!b∣∅ ⟩■
          ! a · ∣ Q′

        (inj₂ (refl , .∅ , Q″ , .b , action , b⟶Q″ , Q′∼!b∣∅∣Q″)) →
          ⊥-elim (names-are-not-inverted b⟶Q″)

    rl {a} (par-τ {P′ = P′} {Q′ = Q′} tr₁ tr₂) =
      case 6-1-3-2 tr₁ ,′ 6-1-3-2 tr₂ of λ where

        (inj₁ (.∅ , action , P′∼!a∣∅) ,
         inj₁ (.∅ , action , Q′∼!co-a∣∅)) →
          ! (a · ⊕ co a ·)              [ τ ]⟶⟨ replication (par-τ (replication (par-right (choice-left action)))
                                                                   (choice-right action)) ⟩ʳˡ
          (! (a · ⊕ co a ·) ∣ ∅) ∣ ∅    ∼⟨ τ-lemma ⟩ ∼′:
          (! a · ∣ ∅) ∣ (! co a · ∣ ∅)  ∼⟨ symmetric (P′∼!a∣∅ ∣-cong Q′∼!co-a∣∅) ⟩■
          P′ ∣ Q′

        (inj₁ _ , inj₂ (() , _))
        (inj₂ (() , _) , _)

  !·⊕·∼′!·∣!· : ∀ {a b i} → [ i ] ! (a · ⊕ b ·) ∼′ ! a · ∣ ! b ·
  force !·⊕·∼′!·∣!· = !·⊕·∼!·∣!·

------------------------------------------------------------------------
-- Exercise 6.2.4

mutual

  -- For a more general result, see 6-2-17-4 below.

  6-2-4 : ∀ {a i} → [ i ] ! ! a · ∼ ! a ·
  6-2-4 {a} {i} = ⟨ lr , rl ⟩
    where
    impossible : ∀ {μ P q} {Q : Set q} →
                 ! ! a · [ μ ]⟶ P → μ ≡ τ → Q
    impossible {μ} !!a⟶P μ≡τ = ⊥-elim $ name≢τ
      (name a  ≡⟨ !-only (!-only ·′-only) !!a⟶P ⟩
       μ       ≡⟨ μ≡τ ⟩∎
       τ       ∎)

    lemma = λ {P} P∼!a∣∅ → ∼′:
      ! ! a · ∣ P            ∼⟨ reflexive ∣-cong P∼!a∣∅ ⟩
      ! ! a · ∣ (! a · ∣ ∅)  ∼⟨ reflexive ∣-cong ∣-right-identity ⟩
      ! ! a · ∣ ! a ·        ∼⟨ 6-1-2 ⟩
      ! ! a ·                ∼⟨ 6-2-4′ {i = i} ⟩ ∼′:
      ! a ·                  ∼⟨ symmetric ∣-right-identity ⟩■
      ! a · ∣ ∅

    lr : ∀ {P μ} →
         ! ! a · [ μ ]⟶ P →
         ∃ λ P′ → ! a · [ μ ]⟶ P′ × [ i ] P ∼′ P′
    lr {P = P} !!a⟶P = case 6-1-3-2 !!a⟶P of λ where
      (inj₂ (μ≡τ , _))               → impossible !!a⟶P μ≡τ
      (inj₁ (P′ , !a⟶P′ , P∼!!a∣P′)) → case 6-1-3-2 !a⟶P′ of λ where
        (inj₂ (μ≡τ , _))               → impossible !!a⟶P μ≡τ
        (inj₁ (.∅ , action , P′∼!a∣∅)) →
          P             ∼⟨ P∼!!a∣P′ ⟩ ∼′:
          ! ! a · ∣ P′  ∼⟨ lemma P′∼!a∣∅ ⟩■
          ! a · ∣ ∅     [ name a ]⟵⟨ replication (par-right action) ⟩
          ! a ·

    rl : ∀ {P μ} →
         ! a · [ μ ]⟶ P →
         ∃ λ P′ → ! ! a · [ μ ]⟶ P′ × [ i ] P′ ∼′ P
    rl {P = P} !a⟶P = case 6-1-3-2 !a⟶P of λ where
      (inj₂ (refl , .∅ , Q″ , .a , action , a⟶Q″ , _)) →
        ⊥-elim (names-are-not-inverted a⟶Q″)
      (inj₁ (.∅ , action , P∼!a∣∅)) →
        ! ! a ·      [ name a ]⟶⟨ replication (par-right !a⟶P) ⟩ʳˡ
        ! ! a · ∣ P  ∼⟨ lemma P∼!a∣∅ ⟩ ∼′:
        ! a · ∣ ∅    ∼⟨ symmetric P∼!a∣∅ ⟩■
        P

  6-2-4′ : ∀ {a i} → [ i ] ! ! a · ∼′ ! a ·
  force 6-2-4′ = 6-2-4

------------------------------------------------------------------------
-- A result mentioned in "Enhancements of the bisimulation proof
-- method"

·∣·∼·· : ∀ {a} → a · ∣ a · ∼ name a · (a ·)
·∣·∼·· {a} = ⟨ lr , rl ⟩
  where
  lr : ∀ {P μ} → a · ∣ a · [ μ ]⟶ P →
       ∃ λ P′ → name a · (a ·) [ μ ]⟶ P′ × P ∼′ P′
  lr (par-left action) =
    ∅ ∣ a ·         ∼⟨ ∣-left-identity ⟩■
    a ·             [ name a ]⟵⟨ action ⟩
    name a · (a ·)

  lr (par-right action) =
    a · ∣ ∅         ∼⟨ ∣-right-identity ⟩■
    a ·             [ name a ]⟵⟨ action ⟩
    name a · (a ·)

  lr (par-τ′ a≡co-a action action) = ⊥-elim (id≢co a≡co-a)

  rl : ∀ {P μ} → name a · (a ·) [ μ ]⟶ P →
       ∃ λ P′ → a · ∣ a · [ μ ]⟶ P′ × P′ ∼′ P
  rl action =
    a · ∣ a ·  [ name a ]⟶⟨ par-right action ⟩ʳˡ
    a · ∣ ∅    ∼⟨ ∣-right-identity ⟩■
    a ·

------------------------------------------------------------------------
-- More preservation lemmas

-- _⊕_ preserves bisimilarity.

infix 8 _⊕-cong_ _⊕-cong′_

_⊕-cong_ : ∀ {i P P′ Q Q′} →
           [ i ] P ∼ P′ → [ i ] Q ∼ Q′ → [ i ] P ⊕ Q ∼ P′ ⊕ Q′
P∼P′ ⊕-cong Q∼Q′ =
  ⟨ CL.⊕-cong P∼P′ Q∼Q′
  , Σ-map id (Σ-map id symmetric) ∘
    CL.⊕-cong (symmetric P∼P′) (symmetric Q∼Q′)
  ⟩

_⊕-cong′_ : ∀ {i P P′ Q Q′} →
            [ i ] P ∼′ P′ → [ i ] Q ∼′ Q′ → [ i ] P ⊕ Q ∼′ P′ ⊕ Q′
force (P∼P′ ⊕-cong′ Q∼Q′) = force P∼P′ ⊕-cong force Q∼Q′

-- _·′_ preserves bisimilarity.

infix 12 _·′-cong_ _·′-cong′_

_·′-cong_ :
  ∀ {i μ μ′ P P′} →
  μ ≡ μ′ → [ i ] force P ∼′ force P′ → [ i ] μ ·′ P ∼ μ′ ·′ P′
refl ·′-cong P∼P′ =
  ⟨ CL.·′-cong P∼P′
  , Σ-map id (Σ-map id symmetric) ∘ CL.·′-cong (symmetric P∼P′)
  ⟩

_·′-cong′_ :
  ∀ {i μ μ′ P P′} →
  μ ≡ μ′ → [ i ] force P ∼′ force P′ → [ i ] μ ·′ P ∼′ μ′ ·′ P′
force (μ≡μ′ ·′-cong′ P∼P′) = μ≡μ′ ·′-cong P∼P′

-- _·_ preserves bisimilarity.

infix 12 _·-cong_ _·-cong′_

_·-cong_ :
  ∀ {i μ μ′ P P′} →
  μ ≡ μ′ → [ i ] P ∼ P′ → [ i ] μ · P ∼ μ′ · P′
refl ·-cong P∼P′ = refl ·′-cong convert {a = ℓ} P∼P′

_·-cong′_ :
  ∀ {i μ μ′ P P′} →
  μ ≡ μ′ → [ i ] P ∼′ P′ → [ i ] μ · P ∼′ μ′ · P′
force (μ≡μ′ ·-cong′ P∼P′) = μ≡μ′ ·-cong force P∼P′

-- _· turns equality into bisimilarity.

infix 12 _·-cong _·-cong′

_·-cong : ∀ {μ μ′} → μ ≡ μ′ → μ · ∼ μ′ ·
refl ·-cong = reflexive

_·-cong′ : ∀ {μ μ′} → μ ≡ μ′ → μ · ∼′ μ′ ·
refl ·-cong′ = reflexive

mutual

  -- !_ preserves bisimilarity.

  infix 10 !-cong_ !-cong′_

  !-cong_ : ∀ {i P P′} →
            [ i ] P ∼ P′ → [ i ] ! P ∼ ! P′
  !-cong P∼P′ =
    ⟨ lr P∼P′
    , Σ-map id (Σ-map id symmetric) ∘ lr (symmetric P∼P′)
    ⟩
    where
    lr = CL.!-cong 6-1-3-2 _∣-cong′_ !-cong′_

  !-cong′_ : ∀ {i P P′} → [ i ] P ∼′ P′ → [ i ] ! P ∼′ ! P′
  force (!-cong′ P∼P′) = !-cong force P∼P′

mutual

  -- ⟨ν_⟩ preserves bisimilarity.

  ⟨ν_⟩-cong : ∀ {i a a′ P P′} →
              a ≡ a′ → [ i ] P ∼ P′ → [ i ] ⟨ν a ⟩ P ∼ ⟨ν a′ ⟩ P′
  ⟨ν refl ⟩-cong = λ P∼P′ →
    ⟨ lr P∼P′
    , Σ-map id (Σ-map id symmetric) ∘ lr (symmetric P∼P′)
    ⟩
    where
    lr = CL.⟨ν⟩-cong ⟨ν refl ⟩-cong′

  ⟨ν_⟩-cong′ : ∀ {i a a′ P P′} →
               a ≡ a′ → [ i ] P ∼′ P′ → [ i ] ⟨ν a ⟩ P ∼′ ⟨ν a′ ⟩ P′
  force (⟨ν a≡a′ ⟩-cong′ P∼P′) = ⟨ν a≡a′ ⟩-cong (force P∼P′)

-- _[_] preserves bisimilarity. (This result is related to Exercise
-- 6.2.10.)

mutual

  infix 5 _[_]-cong _[_]-cong′

  _[_]-cong :
    ∀ {i n Ps Qs}
    (C : Context ∞ n) → (∀ x → [ i ] Ps x ∼ Qs x) →
    [ i ] C [ Ps ] ∼ C [ Qs ]
  hole x   [ Ps∼Qs ]-cong = Ps∼Qs x
  ∅        [ Ps∼Qs ]-cong = reflexive
  C₁ ∣ C₂  [ Ps∼Qs ]-cong = (C₁ [ Ps∼Qs ]-cong) ∣-cong (C₂ [ Ps∼Qs ]-cong)
  C₁ ⊕ C₂  [ Ps∼Qs ]-cong = (C₁ [ Ps∼Qs ]-cong) ⊕-cong (C₂ [ Ps∼Qs ]-cong)
  μ ·′ C   [ Ps∼Qs ]-cong = refl ·′-cong λ { .force → force C [ Ps∼Qs ]-cong }
  ⟨ν a ⟩ C [ Ps∼Qs ]-cong = ⟨ν refl ⟩-cong (C [ Ps∼Qs ]-cong)
  ! C      [ Ps∼Qs ]-cong = !-cong (C [ Ps∼Qs ]-cong)

  _[_]-cong′ :
    ∀ {i n Ps Qs}
    (C : Context ∞ n) → (∀ x → [ i ] Ps x ∼′ Qs x) →
    [ i ] C [ Ps ] ∼′ C [ Qs ]
  force (C [ Ps∼Qs ]-cong′) = C [ (λ x → force (Ps∼Qs x)) ]-cong

-- The proof of _[_]-cong uses 6-1-3-2 (in !-cong_). The following
-- direct proof does not use 6-1-3-2 (but it does use
-- extensionality).

module _ (ext : Proc-extensionality) where

 mutual

  infix 5 _[_]-cong₂ _[_]-cong₂′ _[_]-cong₂″

  _[_]-cong₂ :
    ∀ {i n Ps Qs}
    (C : Context ∞ n) → (∀ x → [ i ] Ps x ∼ Qs x) →
    [ i ] C [ Ps ] ∼ C [ Qs ]
  _[_]-cong₂ {i} C Ps∼Qs =
    ⟨ lr C Ps∼Qs
    , Σ-map id (Σ-map id symmetric) ∘ lr C (symmetric ∘ Ps∼Qs)
    ⟩
    where

    infix 5 _[_][_]-cong₁ _[_][_]-cong₂

    _[_][_]-cong₁ :
      ∀ {n P Q Ps Qs} →
      (C : Context ∞ (suc n)) →
      [ i ] P ∼′ Q →
      (∀ x → [ i ] Ps x ∼ Qs x) →
      [ i ] C [ [ const P , Ps ] ] ∼′ C [ [ const Q , Qs ] ]
    force (C [ P∼′Q ][ Ps∼Qs ]-cong₁) =
      C [ [ const (force P∼′Q) , Ps∼Qs ] ]-cong₂

    _[_][_]-cong₂ :
      ∀ {P Q R S} →
      (C : Context ∞ 2) →
      [ i ] P ∼′ Q →
      [ i ] R ∼′ S →
      [ i ] C [ [ const P , [ const R , (λ ()) ] ] ] ∼′
            C [ [ const Q , [ const S , (λ ()) ] ] ]
    force (C [ P∼′Q ][ R∼′S ]-cong₂) =
      C [ [ const (force P∼′Q)
          , [ const (force R∼′S) , (λ ()) ]
          ] ]-cong₂

    lr : ∀ {n Ps Qs P′ μ} (C : Context ∞ n) →
         (∀ x → [ i ] Ps x ∼ Qs x) →
         C [ Ps ] [ μ ]⟶ P′ →
         ∃ λ Q′ → C [ Qs ] [ μ ]⟶ Q′ × [ i ] P′ ∼′ Q′
    lr (hole x)   Ps∼Qs tr                  = left-to-right (Ps∼Qs x) tr
    lr ∅          Ps∼Qs ()
    lr (C₁ ∣ C₂)  Ps∼Qs (par-left tr)       = Σ-map (_∣ _) (Σ-map par-left (λ b → subst (λ P → [ i ] _ ∼′ _ ∣ P) (ext $ weaken-[] C₂) $
                                                                                  subst (λ P → [ i ] _ ∣ P ∼′ _) (ext $ weaken-[] C₂) $
                                                                                  hole fzero ∣ weaken C₂ [ b ][ Ps∼Qs ]-cong₁)) (lr C₁ Ps∼Qs tr)
    lr (C₁ ∣ C₂)  Ps∼Qs (par-right tr)      = Σ-map (_ ∣_) (Σ-map par-right (λ b → subst (λ P → [ i ] _ ∼′ P ∣ _) (ext $ weaken-[] C₁) $
                                                                                   subst (λ P → [ i ] P ∣ _ ∼′ _) (ext $ weaken-[] C₁) $
                                                                                   weaken C₁ ∣ hole fzero [ b ][ Ps∼Qs ]-cong₁)) (lr C₂ Ps∼Qs tr)
    lr (C₁ ∣ C₂)  Ps∼Qs (par-τ tr₁ tr₂)     = Σ-zip _∣_ (Σ-zip par-τ (λ b₁ b₂ → hole fzero ∣ hole (fsuc fzero) [ b₁ ][ b₂ ]-cong₂))
                                                (lr C₁ Ps∼Qs tr₁) (lr C₂ Ps∼Qs tr₂)
    lr (C₁ ⊕ C₂)  Ps∼Qs (choice-left tr)    = Σ-map id (Σ-map choice-left id) (lr C₁ Ps∼Qs tr)
    lr (C₁ ⊕ C₂)  Ps∼Qs (choice-right tr)   = Σ-map id (Σ-map choice-right id) (lr C₂ Ps∼Qs tr)
    lr (μ ·′ C)   Ps∼Qs action              = _ , action , force C [ Ps∼Qs ]-cong₂′
    lr (⟨ν a ⟩ C) Ps∼Qs (restriction a∉ tr) = Σ-map ⟨ν a ⟩ (Σ-map (restriction a∉) (λ b → ⟨ν a ⟩ (hole fzero) [ b ][ Ps∼Qs ]-cong₁))
                                                (lr C Ps∼Qs tr)
    lr (! C)      Ps∼Qs (replication tr)    = Σ-map id (Σ-map replication id) (lr (! C ∣ C) Ps∼Qs tr)

  _[_]-cong₂′ :
    ∀ {i n Ps Qs}
    (C : Context ∞ n) → (∀ x → [ i ] Ps x ∼ Qs x) →
    [ i ] C [ Ps ] ∼′ C [ Qs ]
  force (C [ Ps∼Qs ]-cong₂′) = C [ Ps∼Qs ]-cong₂

  _[_]-cong₂″ :
    ∀ {i n Ps Qs}
    (C : Context ∞ n) → (∀ x → [ i ] Ps x ∼′ Qs x) →
    [ i ] C [ Ps ] ∼′ C [ Qs ]
  force (C [ Ps∼′Qs ]-cong₂″) = C [ (λ x → force (Ps∼′Qs x)) ]-cong₂

-- Very strong bisimilarity is contained in bisimilarity.

mutual

  ≡→∼ : ∀ {i P Q} → Equal i P Q → [ i ] P ∼ Q
  ≡→∼ ∅              = reflexive
  ≡→∼ (eq₁ ∣ eq₂)    = ≡→∼ eq₁ ∣-cong ≡→∼ eq₂
  ≡→∼ (eq₁ ⊕ eq₂)    = ≡→∼ eq₁ ⊕-cong ≡→∼ eq₂
  ≡→∼ (refl ·′ eq)   = refl ·′-cong ≡→∼′ eq
  ≡→∼ (⟨ν refl ⟩ eq) = ⟨ν refl ⟩-cong (≡→∼ eq)
  ≡→∼ (! eq)         = !-cong ≡→∼ eq

  ≡→∼′ : ∀ {i P Q} → Equal′ i P Q → [ i ] P ∼′ Q
  force (≡→∼′ eq) = ≡→∼ (force eq)

------------------------------------------------------------------------
-- Lemma 6.2.14

mutual

  -- A more general variant of !·⊕·∼!·∣!·. For an even more general
  -- variant, see 6-2-17-2 below.

  6-2-14 :
    ∀ {i a b P Q} →
    [ i ] ! (name a · P ⊕ name b · Q) ∼ ! name a · P ∣ ! name b · Q
  6-2-14 {i} = ⟨ lr , rl ⟩
    where
    left-lemma = λ {a b P Q} → ∼′:
      ! (name a · P ⊕ name b · Q) ∣ P    ∼⟨ 6-2-14′ {i = i} ∣-cong′ reflexive ⟩ ∼′:
      (! name a · P ∣ ! name b · Q) ∣ P  ∼⟨ swap-rightmost ⟩■
      (! name a · P ∣ P) ∣ ! name b · Q

    right-lemma = λ {a b P Q} → ∼′:
      ! (name a · P ⊕ name b · Q) ∣ Q    ∼⟨ 6-2-14′ {i = i} ∣-cong′ reflexive ⟩ ∼′:
      (! name a · P ∣ ! name b · Q) ∣ Q  ∼⟨ symmetric ∣-assoc ⟩■
      ! name a · P ∣ (! name b · Q ∣ Q)

    τ-lemma = λ {a b P Q} → ∼′:
      (! (name a · P ⊕ name b · Q) ∣ P) ∣ Q    ∼⟨ left-lemma ∣-cong′ reflexive ⟩ ∼′:
      ((! name a · P ∣ P) ∣ ! name b · Q) ∣ Q  ∼⟨ symmetric ∣-assoc ⟩■
      (! name a · P ∣ P) ∣ (! name b · Q ∣ Q)

    lr : ∀ {a b P Q R μ} →
         ! (name a · P ⊕ name b · Q) [ μ ]⟶ R →
         ∃ λ S → ! name a · P ∣ ! name b · Q [ μ ]⟶ S × [ i ] R ∼′ S
    lr {a} {b} {P} {Q} {R} tr = case 6-1-3-2 tr of λ where

      (inj₁ (.P , choice-left action , R∼![aP⊕bQ]∣P)) →
        R                                  ∼⟨ R∼![aP⊕bQ]∣P ⟩ ∼′:
        ! (name a · P ⊕ name b · Q) ∣ P    ∼⟨ left-lemma ⟩■
        (! name a · P ∣ P) ∣ ! name b · Q  [ name a ]⟵⟨ par-left (replication (par-right action)) ⟩
        ! name a · P       ∣ ! name b · Q

      (inj₁ (.Q , choice-right action , R∼![aP⊕bQ]∣Q)) →
        R                                  ∼⟨ R∼![aP⊕bQ]∣Q ⟩ ∼′:
        ! (name a · P ⊕ name b · Q) ∣ Q    ∼⟨ right-lemma ⟩■
        ! name a · P ∣ (! name b · Q ∣ Q)  [ name b ]⟵⟨ par-right (replication (par-right action)) ⟩
        ! name a · P ∣ ! name b · Q

      (inj₂ ( refl , R′ , R″ , c , aP⊕bQ⟶R′ , aP⊕bQ⟶R″
            , R∼![aP⊕bQ]∣R′∣R″
            )) →
        let b≡co-a , R′≡,R″≡ = ·′⊕·′-co aP⊕bQ⟶R′ aP⊕bQ⟶R″

            lemma : _ → [ _ ] _ ∼ _
            lemma = λ where
              (inj₁ (R′≡P , R″≡Q)) →
                (! (name a · P ⊕ name b · Q) ∣ R′) ∣ R″  ∼⟨ (reflexive ∣-cong ≡⇒∼ R′≡P) ∣-cong ≡⇒∼ R″≡Q ⟩■
                (! (name a · P ⊕ name b · Q) ∣ P) ∣ Q
              (inj₂ (R′≡Q , R″≡P)) →
                (! (name a · P ⊕ name b · Q) ∣ R′) ∣ R″  ∼⟨ (reflexive ∣-cong ≡⇒∼ R′≡Q) ∣-cong ≡⇒∼ R″≡P ⟩ ∼:
                (! (name a · P ⊕ name b · Q) ∣ Q) ∣ P    ∼⟨ swap-rightmost ⟩■
                (! (name a · P ⊕ name b · Q) ∣ P) ∣ Q
        in
        R                                        ∼⟨ R∼![aP⊕bQ]∣R′∣R″ ⟩
        (! (name a · P ⊕ name b · Q) ∣ R′) ∣ R″  ∼⟨ lemma R′≡,R″≡ ⟩ ∼′:
        (! (name a · P ⊕ name b · Q) ∣ P) ∣ Q    ∼⟨ τ-lemma ⟩■
        (! name a · P ∣ P) ∣ (! name b · Q ∣ Q)  [ τ ]⟵⟨ par-τ′ b≡co-a (replication (par-right action))
                                                                       (replication (par-right action)) ⟩
        ! name a · P ∣ ! name b · Q

    rl : ∀ {a b P Q S μ} →
         ! name a · P ∣ ! name b · Q [ μ ]⟶ S →
         ∃ λ R → ! (name a · P ⊕ name b · Q) [ μ ]⟶ R × [ i ] R ∼′ S
    rl {a} {b} {P} {Q} (par-left {P′ = S} tr) =
      case 6-1-3-2 tr of λ where
        (inj₁ (.P , action , S∼!aP∣P)) →
          ! (name a · P ⊕ name b · Q)        [ name a ]⟶⟨ replication (par-right (choice-left action)) ⟩ʳˡ
          ! (name a · P ⊕ name b · Q) ∣ P    ∼⟨ left-lemma ⟩ ∼′:
          (! name a · P ∣ P) ∣ ! name b · Q  ∼⟨ symmetric S∼!aP∣P ∣-cong reflexive ⟩■
          S ∣ ! name b · Q

        (inj₂ (refl , .P , S′ , .a , action , aP⟶S′ , S∼!aP∣P∣S′)) →
          ⊥-elim (names-are-not-inverted aP⟶S′)

    rl {a} {b} {P} {Q} (par-right {Q′ = S} tr) =
      case 6-1-3-2 tr of λ where
        (inj₁ (.Q , action , S∼!bQ∣Q)) →
          ! (name a · P ⊕ name b · Q)        [ name b ]⟶⟨ replication (par-right (choice-right action)) ⟩ʳˡ
          ! (name a · P ⊕ name b · Q) ∣ Q    ∼⟨ right-lemma ⟩ ∼′:
          ! name a · P ∣ (! name b · Q ∣ Q)  ∼⟨ reflexive ∣-cong symmetric S∼!bQ∣Q ⟩■
          ! name a · P ∣ S

        (inj₂ (refl , .Q , S′ , .b , action , bQ⟶S′ , S∼!bQ∣Q∣S′)) →
          ⊥-elim (names-are-not-inverted bQ⟶S′)

    rl {a} {P = P} {Q} (par-τ {P′ = S} {Q′ = S′} tr₁ tr₂) =
      case 6-1-3-2 tr₁ ,′ 6-1-3-2 tr₂ of λ where
        (inj₁ (.P , action , S∼!aP∣P) ,
         inj₁ (.Q , action , S′∼!co-aQ∣Q)) →
          ! (name a · P ⊕ name (co a) · Q)              [ τ ]⟶⟨ replication (par-τ (replication (par-right (choice-left action)))
                                                                                   (choice-right action)) ⟩ʳˡ
          (! (name a · P ⊕ name (co a) · Q) ∣ P) ∣ Q    ∼⟨ τ-lemma ⟩ ∼′:
          (! name a · P ∣ P) ∣ (! name (co a) · Q ∣ Q)  ∼⟨ symmetric (S∼!aP∣P ∣-cong S′∼!co-aQ∣Q) ⟩■
          S ∣ S′

        (inj₁ _ , inj₂ (() , _))
        (inj₂ (() , _) , _)

  6-2-14′ :
    ∀ {i a b P Q} →
    [ i ] ! (name a · P ⊕ name b · Q) ∼′ ! name a · P ∣ ! name b · Q
  force 6-2-14′ = 6-2-14

------------------------------------------------------------------------
-- Theorem 6.2.16

mutual

  6-2-16 :
    ∀ {i n} {Ps Qs : Fin n → Proc ∞} {C : Fin n → Context ∞ n} →
    (∀ x → Weakly-guarded (C x)) →
    (∀ x → [ i ] Ps x ∼ C x [ Ps ]) →
    (∀ x → [ i ] Qs x ∼ C x [ Qs ]) →
    ∀ x → [ i ] Ps x ∼ Qs x
  6-2-16 {i} {Ps = Ps} {Qs} {C} w ∼C[Ps] ∼C[Qs] x =
    Ps x        ∼⟨ ∼C[Ps] x ⟩
    C x [ Ps ]  ∼⟨ ∼: ⟨ lr ∼C[Ps] ∼C[Qs] , Σ-map id (Σ-map id symmetric) ∘ lr ∼C[Qs] ∼C[Ps] ⟩ ⟩
    C x [ Qs ]  ∼⟨ symmetric (∼C[Qs] x) ⟩■
    Qs x
    where
    lr :
      ∀ {Ps Qs μ P} →
      (∀ x → [ i ] Ps x ∼ C x [ Ps ]) →
      (∀ x → [ i ] Qs x ∼ C x [ Qs ]) →
      C x [ Ps ] [ μ ]⟶ P →
      ∃ λ Q → C x [ Qs ] [ μ ]⟶ Q × [ i ] P ∼′ Q
    lr {Ps} {Qs} {μ} ∼C[Ps] ∼C[Qs] ⟶P =
      case 6-2-15 (C x) (w x) ⟶P of λ where
        (C′ , refl , trs) →
          C′ [ Ps ]   ∼⟨ C′ [ 6-2-16′ w ∼C[Ps] ∼C[Qs] ]-cong′ ⟩■
          C′ [ Qs ]   [ μ ]⟵⟨ trs Qs ⟩
          C x [ Qs ]

  6-2-16′ :
    ∀ {i n} {Ps Qs : Fin n → Proc ∞} {C : Fin n → Context ∞ n} →
    (∀ x → Weakly-guarded (C x)) →
    (∀ x → [ i ] Ps x ∼ C x [ Ps ]) →
    (∀ x → [ i ] Qs x ∼ C x [ Qs ]) →
    ∀ x → [ i ] Ps x ∼′ Qs x
  force (6-2-16′ w ∼C[Ps] ∼C[Qs] x) = 6-2-16 w ∼C[Ps] ∼C[Qs] x

------------------------------------------------------------------------
-- Some lemmas related to _⊕_

-- _⊕_ is idempotent.

⊕-idempotent : ∀ {P} → P ⊕ P ∼ P
⊕-idempotent {P} =
  ⟨ lr
  , (λ {R} P⟶R →
       P ⊕ P  ⟶⟨ choice-left P⟶R ⟩ʳˡ
       R      ∼⟨ ∼′: reflexive ⟩■
       R)
  ⟩
  where
  lr : ∀ {Q μ} → P ⊕ P [ μ ]⟶ Q → ∃ λ R → P [ μ ]⟶ R × Q ∼′ R
  lr {Q} (choice-left P⟶Q) =
    Q  ∼⟨ ∼′: reflexive ⟩■
    Q  ⟵⟨ P⟶Q ⟩
    P

  lr {Q} (choice-right P⟶Q) =
    Q  ∼⟨ ∼′: reflexive ⟩■
    Q  ⟵⟨ P⟶Q ⟩
    P

⊕-idempotent′ : ∀ {P} → P ⊕ P ∼′ P
force ⊕-idempotent′ = ⊕-idempotent

-- _⊕_ is commutative.

⊕-comm : ∀ {P Q} → P ⊕ Q ∼ Q ⊕ P
⊕-comm = ⟨ lr , Σ-map id (Σ-map id symmetric) ∘ lr ⟩
  where
  lr : ∀ {P Q R μ} →
       P ⊕ Q [ μ ]⟶ R → ∃ λ R′ → Q ⊕ P [ μ ]⟶ R′ × R ∼′ R′
  lr {P} {Q} {R} = λ where
    (choice-left  P⟶R) →
      R      ■ ⟵⟨ choice-right P⟶R ⟩
      Q ⊕ P

    (choice-right Q⟶R) →
      R      ■ ⟵⟨ choice-left Q⟶R ⟩
      Q ⊕ P

------------------------------------------------------------------------
-- Lemma 6.2.17

-- Some results mentioned in the proof of 6.2.17 (1) in
-- "Enhancements of the bisimulation proof method".

6-2-17-1-lemma₁ : ∀ {P Q} → (! P ∣ ! Q) ∣ (P ∣ Q) ∼ ! P ∣ ! Q
6-2-17-1-lemma₁ {P} {Q} =
  (! P ∣ ! Q) ∣ (P ∣ Q)  ∼⟨ swap-in-the-middle ⟩ ∼:
  (! P ∣ P) ∣ (! Q ∣ Q)  ∼⟨ 6-1-2 ∣-cong 6-1-2 ⟩■
  ! P ∣ ! Q

abstract

  6-2-17-1-lemma₂ :
    ∀ {P Q R μ} →
    ! (P ∣ Q) [ μ ]⟶ R →
    ∃ λ S →
      R ∼ ! (P ∣ Q) ∣ S ×
      ∃ λ T →
        ! P ∣ ! Q [ μ ]⟶ T ×
        (! P ∣ ! Q) ∣ S ∼′ T
  6-2-17-1-lemma₂ {P} {Q} {R} tr = case 6-1-3-2 tr of λ where
    (inj₁ (R′ , P∣Q⟶R′ , R∼![P∣Q]∣R′)) →
      let R″ , !P∣!Q⟶R″ , !P∣!Q∣R′∼R″ =
            left-to-right
              ((! P ∣ ! Q) ∣ (P ∣ Q)  ∼⟨ 6-2-17-1-lemma₁ ⟩■
               ! P ∣ ! Q)
              ((! P ∣ ! Q) ∣ (P ∣ Q)  ⟶⟨ par-right P∣Q⟶R′ ⟩
               (! P ∣ ! Q) ∣ R′)
      in _ , R∼![P∣Q]∣R′ , _ , !P∣!Q⟶R″ , !P∣!Q∣R′∼R″

    (inj₂ (refl , R′ , R″ , a , P∣Q⟶R′ , P∣Q⟶R″ , R∼![P∣Q]∣R′∣R″)) →
      let T , !P∣!Q⟶T , !P∣!Q∣[R′∣R″]∼T =
            left-to-right
              ((! P ∣ ! Q) ∣ ((P ∣ Q) ∣ (P ∣ Q))  ∼⟨ ∣-assoc ⟩
               ((! P ∣ ! Q) ∣ (P ∣ Q)) ∣ (P ∣ Q)  ∼⟨ 6-2-17-1-lemma₁ ∣-cong reflexive ⟩ ∼:
               (! P ∣ ! Q) ∣ (P ∣ Q)              ∼⟨ 6-2-17-1-lemma₁ ⟩■
               ! P ∣ ! Q)
              ((! P ∣ ! Q) ∣ ((P ∣ Q) ∣ (P ∣ Q))  ⟶⟨ par-right (par-τ P∣Q⟶R′ P∣Q⟶R″) ⟩
               (! P ∣ ! Q) ∣ (R′ ∣ R″))
      in
        _
      , (R                      ∼⟨ R∼![P∣Q]∣R′∣R″ ⟩ ∼:
         (! (P ∣ Q) ∣ R′) ∣ R″  ∼⟨ symmetric ∣-assoc ⟩■
         ! (P ∣ Q) ∣ (R′ ∣ R″))
      , _
      , !P∣!Q⟶T
      , !P∣!Q∣[R′∣R″]∼T

mutual

  6-2-17-1 : ∀ {i P Q} → [ i ] ! (P ∣ Q) ∼ ! P ∣ ! Q
  6-2-17-1 {i} = ⟨ lr , rl ⟩
    where
    lr : ∀ {P Q R μ} →
         ! (P ∣ Q) [ μ ]⟶ R →
         ∃ λ S → ! P ∣ ! Q [ μ ]⟶ S × [ i ] R ∼′ S
    lr {P} {Q} {R} tr =
      let S , R∼![P∣Q]∣S , T , !P∣!Q⟶T , !P∣!Q∣S∼T =
            6-2-17-1-lemma₂ tr in

      R                ∼⟨ R∼![P∣Q]∣S ⟩
      ! (P ∣ Q) ∣ S    ∼⟨ 6-2-17-1′ ∣-cong′ reflexive ⟩ ∼′:
      (! P ∣ ! Q) ∣ S  ∼⟨ !P∣!Q∣S∼T ⟩■
      T                ⟵⟨ !P∣!Q⟶T ⟩
      ! P ∣ ! Q

    lemma = λ {P Q R S} → ∼′:
      ! (P ∣ Q) ∣ (R ∣ S)    ∼⟨ 6-2-17-1′ {i = i} ∣-cong′ reflexive ⟩ ∼′:
      (! P ∣ ! Q) ∣ (R ∣ S)  ∼⟨ swap-in-the-middle ⟩■
      (! P ∣ R) ∣ (! Q ∣ S)

    left-lemma = λ {P Q R} → ∼′:
      ! (P ∣ Q) ∣ (R ∣ Q)    ∼⟨ lemma ⟩ ∼′:
      (! P ∣ R) ∣ (! Q ∣ Q)  ∼⟨ reflexive ∣-cong 6-1-2 ⟩■
      (! P ∣ R) ∣ ! Q

    right-lemma = λ {P Q R} → ∼′:
      ! (P ∣ Q) ∣ (P ∣ R)    ∼⟨ lemma ⟩ ∼′:
      (! P ∣ P) ∣ (! Q ∣ R)  ∼⟨ 6-1-2 ∣-cong reflexive ⟩■
      ! P ∣ (! Q ∣ R)

    rl : ∀ {P Q S μ} →
         ! P ∣ ! Q [ μ ]⟶ S →
         ∃ λ R → ! (P ∣ Q) [ μ ]⟶ R × [ i ] R ∼′ S
    rl {P} {Q} (par-left {P′ = S} !P⟶S) =
      case 6-1-3-2 !P⟶S
        return (const $ ∃ λ _ → _ × [ i ] _ ∼′ _)
        of λ where
        (inj₁ (P′ , P⟶P′ , S∼!P∣P′)) →
          ! (P ∣ Q)             ⟶⟨ replication (par-right (par-left P⟶P′)) ⟩ʳˡ
          ! (P ∣ Q) ∣ (P′ ∣ Q)  ∼⟨ left-lemma ⟩ ∼′:
          (! P ∣ P′) ∣ ! Q      ∼⟨ symmetric S∼!P∣P′ ∣-cong reflexive ⟩■
          S ∣ ! Q

        (inj₂ (refl , P′ , P″ , a , P⟶P′ , P⟶P″ , S∼!P∣P′∣P″)) →
          ! (P ∣ Q)                          [ τ ]⟶⟨ replication (par-τ (replication (par-right (par-left P⟶P′)))
                                                                        (par-left P⟶P″)) ⟩ʳˡ
          (! (P ∣ Q) ∣ (P′ ∣ Q)) ∣ (P″ ∣ Q)  ∼⟨ left-lemma ∣-cong′ reflexive ⟩
          ((! P ∣ P′) ∣ ! Q) ∣ (P″ ∣ Q)      ∼⟨ swap-in-the-middle ⟩
          ((! P ∣ P′) ∣ P″) ∣ (! Q ∣ Q)      ∼⟨ reflexive ∣-cong 6-1-2 ⟩ ∼′:
          ((! P ∣ P′) ∣ P″) ∣ ! Q            ∼⟨ symmetric S∼!P∣P′∣P″ ∣-cong reflexive ⟩■
          S ∣ ! Q

    rl {P} {Q} (par-right {Q′ = S} !Q⟶S) =
      case 6-1-3-2 !Q⟶S
        return (const $ ∃ λ _ → _ × [ i ] _ ∼′ _)
        of λ where
        (inj₁ (Q′ , Q⟶Q′ , S∼!Q∣Q′)) →
          ! (P ∣ Q)             ⟶⟨ replication (par-right (par-right Q⟶Q′)) ⟩ʳˡ
          ! (P ∣ Q) ∣ (P ∣ Q′)  ∼⟨ right-lemma ⟩ ∼′:
          ! P ∣ (! Q ∣ Q′)      ∼⟨ reflexive ∣-cong symmetric S∼!Q∣Q′ ⟩■
          ! P ∣ S

        (inj₂ (refl , Q′ , Q″ , a , Q⟶Q′ , Q⟶Q″ , S∼!Q∣Q′∣Q″)) →
          ! (P ∣ Q)                          [ τ ]⟶⟨ replication (par-τ (replication (par-right (par-right Q⟶Q′)))
                                                                        (par-right Q⟶Q″)) ⟩ʳˡ
          (! (P ∣ Q) ∣ (P ∣ Q′)) ∣ (P ∣ Q″)  ∼⟨ right-lemma ∣-cong′ reflexive ⟩
          (! P ∣ (! Q ∣ Q′)) ∣ (P ∣ Q″)      ∼⟨ swap-in-the-middle ⟩
          (! P ∣ P) ∣ ((! Q ∣ Q′) ∣ Q″)      ∼⟨ 6-1-2 ∣-cong reflexive ⟩ ∼′:
          ! P ∣ ((! Q ∣ Q′) ∣ Q″)            ∼⟨ reflexive ∣-cong symmetric S∼!Q∣Q′∣Q″ ⟩■
          ! P ∣ S

    rl {P} {Q} (par-τ {P′ = S} {Q′ = S′} !P⟶S !Q⟶S′) =
      case 6-1-3-2 !P⟶S ,′ 6-1-3-2 !Q⟶S′ of λ where
        (inj₁ (P′ , P⟶P′ , S∼!P∣P′) ,
         inj₁ (Q′ , Q⟶Q′ , S′∼!Q∣Q′)) →
          ! (P ∣ Q)                          [ τ ]⟶⟨ replication (par-τ (replication (par-right (par-left P⟶P′)))
                                                                                     (par-right Q⟶Q′)) ⟩ʳˡ
          (! (P ∣ Q) ∣ (P′ ∣ Q)) ∣ (P ∣ Q′)  ∼⟨ left-lemma ∣-cong′ reflexive ⟩
          ((! P ∣ P′) ∣ ! Q) ∣ (P ∣ Q′)      ∼⟨ swap-in-the-middle ⟩
          ((! P ∣ P′) ∣ P) ∣ (! Q ∣ Q′)      ∼⟨ swap-rightmost ∣-cong reflexive ⟩
          ((! P ∣ P) ∣ P′) ∣ (! Q ∣ Q′)      ∼⟨ (6-1-2 ∣-cong reflexive) ∣-cong reflexive ⟩ ∼′:
          (! P ∣ P′) ∣ (! Q ∣ Q′)            ∼⟨ symmetric (S∼!P∣P′ ∣-cong S′∼!Q∣Q′) ⟩■
          S ∣ S′

        (inj₁ _ , inj₂ (() , _))
        (inj₂ (() , _) , _)

  6-2-17-1′ : ∀ {i P Q} → [ i ] ! (P ∣ Q) ∼′ ! P ∣ ! Q
  force 6-2-17-1′ = 6-2-17-1

mutual

  6-2-17-2 : ∀ {i P Q} → [ i ] ! (P ⊕ Q) ∼ ! P ∣ ! Q
  6-2-17-2 {i} = ⟨ lr , rl ⟩
    where
    left-lemma = λ {P Q R} → ∼′:
      ! (P ⊕ Q) ∣ R    ∼⟨ 6-2-17-2′ {i = i} ∣-cong′ reflexive ⟩ ∼′:
      (! P ∣ ! Q) ∣ R  ∼⟨ swap-rightmost ⟩■
      (! P ∣ R) ∣ ! Q

    right-lemma = λ {P Q R} → ∼′:
      ! (P ⊕ Q) ∣ R    ∼⟨ 6-2-17-2′ {i = i} ∣-cong′ reflexive ⟩ ∼′:
      (! P ∣ ! Q) ∣ R  ∼⟨ symmetric ∣-assoc ⟩■
      ! P ∣ (! Q ∣ R)

    τ-lemma₁ = λ {P P′ P″ Q} → ∼′:
      (! (P ⊕ Q) ∣ P′) ∣ P″    ∼⟨ left-lemma ∣-cong′ reflexive ⟩ ∼′:
      ((! P ∣ P′) ∣ ! Q) ∣ P″  ∼⟨ swap-rightmost ⟩■
      ((! P ∣ P′) ∣ P″) ∣ ! Q

    τ-lemma₂ = λ {P P′ Q Q′} → ∼′:
      (! (P ⊕ Q) ∣ P′) ∣ Q′    ∼⟨ left-lemma ∣-cong′ reflexive ⟩ ∼′:
      ((! P ∣ P′) ∣ ! Q) ∣ Q′  ∼⟨ symmetric ∣-assoc ⟩■
      (! P ∣ P′) ∣ (! Q ∣ Q′)

    τ-lemma₃ = λ {P Q Q′ Q″} → ∼′:
      (! (P ⊕ Q) ∣ Q′) ∣ Q″    ∼⟨ right-lemma ∣-cong′ reflexive ⟩ ∼′:
      (! P ∣ (! Q ∣ Q′)) ∣ Q″  ∼⟨ symmetric ∣-assoc ⟩■
      ! P ∣ ((! Q ∣ Q′) ∣ Q″)

    lr : ∀ {P Q R μ} →
         ! (P ⊕ Q) [ μ ]⟶ R →
         ∃ λ S → ! P ∣ ! Q [ μ ]⟶ S × [ i ] R ∼′ S
    lr {P} {Q} {R} tr =
      case 6-1-3-2 tr
        return (const $ ∃ λ _ → _ × [ i ] _ ∼′ _)
        of λ where

        (inj₁ (P′ , choice-left P⟶P′ , R∼![P⊕Q]∣P′)) →
          R                 ∼⟨ R∼![P⊕Q]∣P′ ⟩ ∼′:
          ! (P ⊕ Q) ∣ P′    ∼⟨ left-lemma ⟩■
          (! P ∣ P′) ∣ ! Q  ⟵⟨ par-left (replication (par-right P⟶P′)) ⟩
          ! P        ∣ ! Q

        (inj₁ (Q′ , choice-right Q⟶Q′ , R∼![P⊕Q]∣Q′)) →
          R                 ∼⟨ R∼![P⊕Q]∣Q′ ⟩ ∼′:
          ! (P ⊕ Q) ∣ Q′    ∼⟨ right-lemma ⟩■
          ! P ∣ (! Q ∣ Q′)  ⟵⟨ par-right (replication (par-right Q⟶Q′)) ⟩
          ! P ∣  ! Q

        (inj₂ ( refl , P′ , P″ , c
              , choice-left P⟶P′ , choice-left P⟶P″
              , R∼![P⊕Q]∣P′∣P″
              )) →
          R                        ∼⟨ R∼![P⊕Q]∣P′∣P″ ⟩ ∼′:
          (! (P ⊕ Q) ∣ P′) ∣ P″    ∼⟨ τ-lemma₁ ⟩■
          ((! P ∣ P′) ∣ P″) ∣ ! Q  [ τ ]⟵⟨ par-left (replication (par-τ (replication (par-right P⟶P′)) P⟶P″)) ⟩
          ! P ∣ ! Q

        (inj₂ ( refl , P′ , Q′ , c
              , choice-left P⟶P′ , choice-right Q⟶Q′
              , R∼![P⊕Q]∣P′∣Q′
              )) →
          R                        ∼⟨ R∼![P⊕Q]∣P′∣Q′ ⟩ ∼′:
          (! (P ⊕ Q) ∣ P′) ∣ Q′    ∼⟨ τ-lemma₂ ⟩■
          (! P ∣ P′) ∣ (! Q ∣ Q′)  [ τ ]⟵⟨ par-τ (replication (par-right P⟶P′))
                                                 (replication (par-right Q⟶Q′)) ⟩
          ! P ∣ ! Q

        (inj₂ ( refl , Q′ , P′ , c
              , choice-right Q⟶Q′ , choice-left P⟶P′
              , R∼![P⊕Q]∣Q′∣P′
              )) →
          R                        ∼⟨ R∼![P⊕Q]∣Q′∣P′ ⟩
          (! (P ⊕ Q) ∣ Q′) ∣ P′    ∼⟨ right-lemma ∣-cong′ reflexive ⟩ ∼′:
          (! P ∣ (! Q ∣ Q′)) ∣ P′  ∼⟨ swap-rightmost ⟩■
          (! P ∣ P′) ∣ (! Q ∣ Q′)  [ τ ]⟵⟨ par-τ′ (sym $ co-involutive c)
                                                  (replication (par-right P⟶P′))
                                                  (replication (par-right Q⟶Q′)) ⟩
          ! P ∣ ! Q

        (inj₂ ( refl , Q′ , Q″ , c
              , choice-right Q⟶Q′ , choice-right Q⟶Q″
              , R∼![P⊕Q]∣Q′∣Q″
              )) →
          R                        ∼⟨ R∼![P⊕Q]∣Q′∣Q″ ⟩ ∼′:
          (! (P ⊕ Q) ∣ Q′) ∣ Q″    ∼⟨ τ-lemma₃ ⟩■
          ! P ∣ ((! Q ∣ Q′) ∣ Q″)  [ τ ]⟵⟨ par-right (replication (par-τ (replication (par-right Q⟶Q′)) Q⟶Q″)) ⟩
          ! P ∣ ! Q

    rl : ∀ {P Q S μ} →
         ! P ∣ ! Q [ μ ]⟶ S →
         ∃ λ R → ! (P ⊕ Q) [ μ ]⟶ R × [ i ] R ∼′ S
    rl {P} {Q} (par-left {P′ = S} !P⟶S) =
      case 6-1-3-2 !P⟶S
        return (const $ ∃ λ _ → _ × [ i ] _ ∼′ _)
        of λ where
        (inj₁ (P′ , P⟶P′ , S∼!P∣P′)) →
          ! (P ⊕ Q)         ⟶⟨ replication (par-right (choice-left P⟶P′)) ⟩ʳˡ
          ! (P ⊕ Q) ∣ P′    ∼⟨ left-lemma ⟩ ∼′:
          (! P ∣ P′) ∣ ! Q  ∼⟨ symmetric S∼!P∣P′ ∣-cong reflexive ⟩■
          S ∣ ! Q

        (inj₂ (refl , P′ , P″ , a , P⟶P′ , P⟶P″ , S∼!P∣P′∣P″)) →
          ! (P ⊕ Q)                [ τ ]⟶⟨ replication (par-τ (replication (par-right (choice-left P⟶P′)))
                                                              (choice-left P⟶P″)) ⟩ʳˡ
          (! (P ⊕ Q) ∣ P′) ∣ P″    ∼⟨ τ-lemma₁ ⟩ ∼′:
          ((! P ∣ P′) ∣ P″) ∣ ! Q  ∼⟨ symmetric S∼!P∣P′∣P″ ∣-cong reflexive ⟩■
          S ∣ ! Q

    rl {P} {Q} (par-right {Q′ = S} !Q⟶S) =
      case 6-1-3-2 !Q⟶S
        return (const $ ∃ λ _ → _ × [ i ] _ ∼′ _)
        of λ where
        (inj₁ (Q′ , Q⟶Q′ , S∼!Q∣Q′)) →
          ! (P ⊕ Q)         ⟶⟨ replication (par-right (choice-right Q⟶Q′)) ⟩ʳˡ
          ! (P ⊕ Q) ∣ Q′    ∼⟨ right-lemma ⟩ ∼′:
          ! P ∣ (! Q ∣ Q′)  ∼⟨ reflexive ∣-cong symmetric S∼!Q∣Q′ ⟩■
          ! P ∣ S

        (inj₂ (refl , Q′ , Q″ , a , Q⟶Q′ , Q⟶Q″ , S∼!Q∣Q′∣Q″)) →
          ! (P ⊕ Q)                [ τ ]⟶⟨ replication (par-τ (replication (par-right (choice-right Q⟶Q′)))
                                                              (choice-right Q⟶Q″)) ⟩ʳˡ
          (! (P ⊕ Q) ∣ Q′) ∣ Q″    ∼⟨ τ-lemma₃ ⟩ ∼′:
          ! P ∣ ((! Q ∣ Q′) ∣ Q″)  ∼⟨ reflexive ∣-cong symmetric S∼!Q∣Q′∣Q″ ⟩■
          ! P ∣ S

    rl {P} {Q} (par-τ {P′ = S} {Q′ = S′} !P⟶S !Q⟶S′) =
      case 6-1-3-2 !P⟶S ,′ 6-1-3-2 !Q⟶S′ of λ where
        (inj₁ (P′ , P⟶P′ , S∼!P∣P′) ,
         inj₁ (Q′ , Q⟶Q′ , S′∼!Q∣Q′)) →
          ! (P ⊕ Q)                [ τ ]⟶⟨ replication (par-τ (replication (par-right (choice-left P⟶P′)))
                                                                                      (choice-right Q⟶Q′)) ⟩ʳˡ
          (! (P ⊕ Q) ∣ P′) ∣ Q′    ∼⟨ τ-lemma₂ ⟩ ∼′:
          (! P ∣ P′) ∣ (! Q ∣ Q′)  ∼⟨ symmetric (S∼!P∣P′ ∣-cong S′∼!Q∣Q′) ⟩■
          S ∣ S′

        (inj₁ _ , inj₂ (() , _))
        (inj₂ (() , _) , _)

  6-2-17-2′ : ∀ {i P Q} → [ i ] ! (P ⊕ Q) ∼′ ! P ∣ ! Q
  force 6-2-17-2′ = 6-2-17-2

6-2-17-3 : ∀ {P} → ! P ∣ ! P ∼ ! P
6-2-17-3 {P} =
  ! P ∣ ! P  ∼⟨ symmetric 6-2-17-2 ⟩ ∼:
  ! (P ⊕ P)  ∼⟨ !-cong ⊕-idempotent ⟩■
  ! P

-- A result mentioned in the proof of 6.2.17 (4) in "Enhancements of
-- the bisimulation proof method".

6-2-17-4-lemma : ∀ {P Q μ} → ! P [ μ ]⟶ Q → Q ∼ ! P ∣ Q
6-2-17-4-lemma {P} {Q} !P⟶Q = case 6-1-3-2 !P⟶Q of λ where
  (inj₁ (P′ , P⟶P′ , Q∼!P∣P′)) →
    Q                 ∼⟨ Q∼!P∣P′ ⟩
    ! P ∣ P′          ∼⟨ symmetric 6-2-17-3 ∣-cong reflexive ⟩
    (! P ∣ ! P) ∣ P′  ∼⟨ symmetric ∣-assoc ⟩ ∼:
    ! P ∣ (! P ∣ P′)  ∼⟨ reflexive ∣-cong symmetric Q∼!P∣P′ ⟩■
    ! P ∣ Q

  (inj₂ (_ , P′ , P″ , _ , P⟶P′ , P⟶P″ , Q∼!P∣P′∣P″)) →
    Q                        ∼⟨ Q∼!P∣P′∣P″ ⟩
    (! P ∣ P′) ∣ P″          ∼⟨ symmetric ∣-assoc ⟩
    ! P ∣ (P′ ∣ P″)          ∼⟨ symmetric 6-2-17-3 ∣-cong reflexive ⟩
    (! P ∣ ! P) ∣ (P′ ∣ P″)  ∼⟨ symmetric ∣-assoc ⟩
    ! P ∣ (! P ∣ (P′ ∣ P″))  ∼⟨ reflexive ∣-cong ∣-assoc ⟩ ∼:
    ! P ∣ ((! P ∣ P′) ∣ P″)  ∼⟨ reflexive ∣-cong symmetric Q∼!P∣P′∣P″ ⟩■
    ! P ∣ Q

mutual

  6-2-17-4 : ∀ {P i} → [ i ] ! ! P ∼ ! P
  6-2-17-4 {P} {i} = ⟨ lr , rl ⟩
    where
    lemma = λ {Q μ} (!P⟶Q : ! P [ μ ]⟶ Q) → ∼′:
      ! ! P ∣ Q  ∼⟨ 6-2-17-4′ {i = i} ∣-cong′ reflexive ⟩ ∼′:
      ! P ∣ Q    ∼⟨ symmetric (6-2-17-4-lemma !P⟶Q) ⟩■
      Q

    lr : ∀ {Q μ} →
         ! ! P [ μ ]⟶ Q →
         ∃ λ Q′ → ! P [ μ ]⟶ Q′ × [ i ] Q ∼′ Q′
    lr {Q} !!P⟶Q = case 6-1-3-2 !!P⟶Q of λ where
      (inj₁ (Q′ , !P⟶Q′ , Q∼!!P∣Q′)) →
        Q           ∼⟨ Q∼!!P∣Q′ ⟩ ∼′:
        ! ! P ∣ Q′  ∼⟨ lemma !P⟶Q′ ⟩■
        Q′          ⟵⟨ !P⟶Q′ ⟩
        ! P

      (inj₂ (refl , Q′ , Q″ , a , !P⟶Q′ , !P⟶Q″ , Q∼!!P∣Q′∣Q″)) →
        case 6-1-3-2 !P⟶Q″ of λ where
          (inj₂ (() , _))
          (inj₁ (Q‴ , P⟶Q‴ , Q″∼!P∣Q‴)) →
            let !P⟶Q′∣Q″ =
                  ! P      [ τ ]⟶⟨ replication (par-τ !P⟶Q′ P⟶Q‴) ⟩
                  Q′ ∣ Q‴
            in
            Q                          ∼⟨ Q∼!!P∣Q′∣Q″ ⟩
            (! ! P ∣ Q′) ∣ Q″          ∼⟨ reflexive ∣-cong Q″∼!P∣Q‴ ⟩
            (! ! P ∣ Q′) ∣ (! P ∣ Q‴)  ∼⟨ swap-in-the-middle ⟩
            (! ! P ∣ ! P) ∣ (Q′ ∣ Q‴)  ∼⟨ 6-1-2 ∣-cong reflexive ⟩ ∼′:
            ! ! P ∣ (Q′ ∣ Q‴)          ∼⟨ lemma !P⟶Q′∣Q″ ⟩■
            Q′ ∣ Q‴                    [ τ ]⟵⟨ !P⟶Q′∣Q″ ⟩
            ! P

    rl : ∀ {Q μ} →
         ! P [ μ ]⟶ Q →
         ∃ λ Q′ → ! ! P [ μ ]⟶ Q′ × [ i ] Q′ ∼′ Q
    rl {Q} !P⟶Q =
      ! ! P      ⟶⟨ replication (par-right !P⟶Q) ⟩ʳˡ
      ! ! P ∣ Q  ∼⟨ lemma !P⟶Q ⟩■
      Q

  6-2-17-4′ : ∀ {P i} → [ i ] ! ! P ∼′ ! P
  force 6-2-17-4′ = 6-2-17-4

------------------------------------------------------------------------
-- An example from "Coinduction All the Way Up" by Pous

module _ (a b : Name-with-kind) where

  A B C D : ∀ {i} → Proc i

  A = name a · name b · D
  B = name a · name b · C

  C = name (co a) ·′ λ { .force → A ∣ C }
  D = name (co a) ·′ λ { .force → B ∣ D }

  mutual

    A∼B : ∀ {i} → [ i ] A ∼ B
    A∼B = refl ·-cong (refl ·-cong symmetric C∼D)

    C∼D : ∀ {i} → [ i ] C ∼ D
    C∼D = refl ·′-cong λ { .force → A∼B ∣-cong C∼D }

------------------------------------------------------------------------
-- Some other examples

Restricted : Name → Proc ∞
Restricted a = ⟨ν a ⟩ (name (a , true) · ∅)

Restricted∼∅ : ∀ {a} → Restricted a ∼ ∅
Restricted∼∅ =
  ⟨ (λ { (restriction x≢x action) → ⊥-elim (x≢x refl) })
  , (λ ())
  ⟩

module Another-example (a : Name) (μ : Action) where

  P : ∀ {i} → Proc i
  P = Restricted a ∣ (μ ·′ λ { .force → P })

  Q : ∀ {i} → Proc i
  Q = μ ·′ λ { .force → Q }

  P∼Q : ∀ {i} → [ i ] P ∼ Q
  P∼Q = P      ∼⟨ Restricted∼∅ ∣-cong (refl ·′-cong λ { .force → P∼Q }) ⟩
        ∅ ∣ Q  ∼⟨ ∣-left-identity ⟩■
        Q
