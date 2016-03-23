------------------------------------------------------------------------
-- Some exercises and results from "Enhancements of the bisimulation
-- proof method" by Pous and Sangiorgi
--
-- Implemented using the classical definition of bisimilarity.
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Bisimilarity.Exercises.Classical where

open import Equality.Propositional hiding (reflexive)
open import Logical-equivalence using (_⇔_)
open import Prelude

open import Function-universe equality-with-J hiding (id; _∘_)

open import Labelled-transition-system
open import Bisimilarity.Classical.Preliminaries
import Bisimilarity.Classical
open import Bisimilarity.Comparison
import Bisimilarity.Exercises.Other

module _ {Name : Set} where

  open CCS Name
  open LTS CCS using (step-with-action)
  open Bisimilarity.Classical CCS

  ------------------------------------------------------------------------
  -- Various lemmas related to _∣_

  -- _∣_ is commutative.

  ∣-comm : ∀ {P Q} → P ∣ Q ∼ Q ∣ P
  ∣-comm = _R_ , R-is-a-bisimulation , base
    where
    data _R_ : Proc → Proc → Set where
      base : ∀ {P Q} → (P ∣ Q) R (Q ∣ P)

    R-is-symmetric : ∀ {P Q} → P R Q → Q R P
    R-is-symmetric base = base

    R-is-a-bisimulation : Bisimulation _R_
    R-is-a-bisimulation =
      ⟨ lr , (λ PRQ tr →
                Σ-map id (Σ-map id R-is-symmetric)
                  (lr (R-is-symmetric PRQ) tr)) ⟩
      where
      lr : ∀ {P P′ Q μ} →
           P R Q → P [ μ ]⟶ P′ →
           ∃ λ Q′ → Q [ μ ]⟶ Q′ × P′ R Q′
      lr base (par-left  tr)  = _ , par-right tr , base
      lr base (par-right tr)  = _ , par-left  tr , base
      lr base (par-τ tr₁ tr₂) =
          _
        , par-τ tr₂ (subst (λ a → _ [ name a ]⟶ _)
                           (sym $ co-involutive _)
                           tr₁)
        , base

  -- _∣_ is associative.

  ∣-assoc : ∀ {P Q R} → P ∣ (Q ∣ R) ∼ (P ∣ Q) ∣ R
  ∣-assoc = _S_ , S-is-a-bisimulation , base
    where
    data _S_ : Proc → Proc → Set where
      base : ∀ {P Q R} → (P ∣ (Q ∣ R)) S ((P ∣ Q) ∣ R)

    S-is-a-bisimulation : Bisimulation _S_
    S-is-a-bisimulation = ⟨ lr , rl ⟩
      where
      lr : ∀ {P P′ Q μ} →
           P S Q → P [ μ ]⟶ P′ →
           ∃ λ Q′ → Q [ μ ]⟶ Q′ × P′ S Q′
      lr base (par-left tr)               = _ , par-left (par-left tr)    , base
      lr base (par-right (par-left tr))   = _ , par-left (par-right tr)   , base
      lr base (par-right (par-right tr))  = _ , par-right tr              , base
      lr base (par-right (par-τ tr₁ tr₂)) = _ , par-τ (par-right tr₁) tr₂ , base
      lr base (par-τ tr₁ (par-left tr₂))  = _ , par-left (par-τ tr₁ tr₂)  , base
      lr base (par-τ tr₁ (par-right tr₂)) = _ , par-τ (par-left tr₁) tr₂  , base

      rl : ∀ {P Q Q′ μ} →
           P S Q → Q [ μ ]⟶ Q′ →
           ∃ λ P′ → P [ μ ]⟶ P′ × P′ S Q′
      rl base (par-left (par-left tr))    = _ , par-left tr               , base
      rl base (par-left (par-right tr))   = _ , par-right (par-left tr)   , base
      rl base (par-left (par-τ tr₁ tr₂))  = _ , par-τ tr₁ (par-left tr₂)  , base
      rl base (par-right tr)              = _ , par-right (par-right tr)  , base
      rl base (par-τ (par-left tr₁) tr₂)  = _ , par-τ tr₁ (par-right tr₂) , base
      rl base (par-τ (par-right tr₁) tr₂) = _ , par-right (par-τ tr₁ tr₂) , base

  -- ∅ is a left identity of _∣_.

  ∣-left-identity : ∀ {P} → ∅ ∣ P ∼ P
  ∣-left-identity = _R_ , R-is-a-bisimulation , base
    where
    data _R_ : Proc → Proc → Set where
      base : ∀ {P} → (∅ ∣ P) R P

    R-is-a-bisimulation : Bisimulation _R_
    R-is-a-bisimulation = ⟨ lr , rl ⟩
      where
      lr : ∀ {P P′ Q μ} →
           P R Q → P [ μ ]⟶ P′ →
           ∃ λ Q′ → Q [ μ ]⟶ Q′ × P′ R Q′
      lr base (par-right tr) = _ , tr , base
      lr base (par-left ())
      lr base (par-τ () _)

      rl : ∀ {P Q Q′ μ} →
           P R Q → Q [ μ ]⟶ Q′ →
           ∃ λ P′ → P [ μ ]⟶ P′ × P′ R Q′
      rl base tr = _ , par-right tr , base

  -- ∅ is a right identity of _∣_.

  ∣-right-identity : ∀ {P} → P ∣ ∅ ∼ P
  ∣-right-identity {P} =
    P ∣ ∅  ∼⟨ ∣-comm ⟩
    ∅ ∣ P  ∼⟨ ∣-left-identity ⟩∎
    P

  -- _∣_ preserves bisimilarity.

  _∣-cong_ : ∀ {P P′ Q Q′} → P ∼ P′ → Q ∼ Q′ → P ∣ Q ∼ P′ ∣ Q′
  (_L_ , ⟨ lrˡ , rlˡ ⟩ , PLP′) ∣-cong (_R_ , ⟨ lrʳ , rlʳ ⟩ , QRQ′) =
    _LR_ , ⟨ lr , rl ⟩ , base PLP′ QRQ′
    where
    data _LR_ : Proc → Proc → Set where
      base : ∀ {P P′ Q Q′} → P L P′ → Q R Q′ → (P ∣ Q) LR (P′ ∣ Q′)

    lr : ∀ {P P′ Q μ} →
         P LR Q → P [ μ ]⟶ P′ →
         ∃ λ Q′ → Q [ μ ]⟶ Q′ × P′ LR Q′
    lr (base PLP′ QRQ′) (par-left tr) =
      Σ-map (_∣ _) (Σ-map par-left (flip base QRQ′)) (lrˡ PLP′ tr)

    lr (base PLP′ QRQ′) (par-right tr) =
      Σ-map (_ ∣_) (Σ-map par-right (base PLP′)) (lrʳ QRQ′ tr)

    lr (base PLP′ QRQ′) (par-τ tr₁ tr₂) =
      Σ-zip _∣_ (Σ-zip par-τ base) (lrˡ PLP′ tr₁) (lrʳ QRQ′ tr₂)

    rl : ∀ {P Q Q′ μ} →
         P LR Q → Q [ μ ]⟶ Q′ →
         ∃ λ P′ → P [ μ ]⟶ P′ × P′ LR Q′
    rl (base PLP′ QRQ′) (par-left tr) =
      Σ-map (_∣ _) (Σ-map par-left (flip base QRQ′)) (rlˡ PLP′ tr)

    rl (base PLP′ QRQ′) (par-right tr) =
      Σ-map (_ ∣_) (Σ-map par-right (base PLP′)) (rlʳ QRQ′ tr)

    rl (base PLP′ QRQ′) (par-τ tr₁ tr₂) =
      Σ-zip _∣_ (Σ-zip par-τ base) (rlˡ PLP′ tr₁) (rlʳ QRQ′ tr₂)

  ----------------------------------------------------------------------
  -- Exercise 6.1.2

  6-1-2 : ∀ {P} → ! P ∣ P ∼ ! P
  6-1-2 {P} = _R_ , R-is-a-bisimulation , base
    where
    data _R_ : Proc → Proc → Set where
      base : (! P ∣ P) R (! P)
      refl : ∀ {P} → P R P

    R-is-a-bisimulation : Bisimulation _R_
    R-is-a-bisimulation = ⟨ lr , rl ⟩
      where
      lr : ∀ {P P′ Q μ} →
           P R Q → P [ μ ]⟶ P′ →
           ∃ λ Q′ → Q [ μ ]⟶ Q′ × P′ R Q′
      lr base tr = _ , replication tr , refl
      lr refl tr = _ , tr             , refl

      rl : ∀ {P Q Q′ μ} →
           P R Q → Q [ μ ]⟶ Q′ →
           ∃ λ P′ → P [ μ ]⟶ P′ × P′ R Q′
      rl base (replication tr) = _ , tr , refl
      rl refl tr               = _ , tr , refl

  ----------------------------------------------------------------------
  -- Exercise 6.1.3 (2)

  open Bisimilarity.Exercises.Other.6-1-3-2 (record
         { _∼_       = _∼_
         ; _∼⟨_⟩_    = _∼⟨_⟩_
         ; finally-∼ = finally-∼
         ; reflexive = reflexive
         ; symmetric = symmetric
         ; ∣-comm    = ∣-comm
         ; ∣-assoc   = ∣-assoc
         ; _∣-cong_  = _∣-cong_
         ; 6-1-2     = 6-1-2
         })
         public using (swap-rightmost; 6-1-3-2)

  ----------------------------------------------------------------------
  -- Exercise 6.2.4

  6-2-4 : ∀ {a} → ! ! a · ∼ ! a ·
  6-2-4 {a} =
    _⇔_.to larger⇔smallest (bisimulation-up-to-∼⊆∼ R-is _ _ base)
    where
    data _R_ : Proc → Proc → Set where
      base : (! ! a ·) R (! a ·)

    impossible : ∀ {μ P q} {Q : Set q} →
                 ! ! a · [ μ ]⟶ P → μ ≡ τ → Q
    impossible {μ} !!a⟶P μ≡τ = ⊥-elim $ name≢τ
      (name a  ≡⟨ !-only (!-only ·-only) !!a⟶P ⟩
       μ       ≡⟨ μ≡τ ⟩∎
       τ       ∎)

    R-is : Bisimulation-up-to-bisimilarity lzero _R_
    R-is = ⟨ lr , rl ⟩
      where
      lemma = λ {P} P∼!a∣∅ →
        ! ! a · ∣ P            ∼⟨ reflexive ∣-cong P∼!a∣∅ ⟩
        ! ! a · ∣ (! a · ∣ ∅)  ∼⟨ reflexive ∣-cong ∣-right-identity ⟩
        ! ! a · ∣ ! a ·        ∼⟨ 6-1-2 ⟩∎
        ! ! a ·

      lr : ∀ {P P′ Q μ} →
           P R Q → P [ μ ]⟶ P′ →
           ∃ λ Q′ → Q [ μ ]⟶ Q′ × (_∼_ ⊙ _R_ ⊙ _∼_) P′ Q′
      lr {P′ = P′} base !!a⟶P′ with 6-1-3-2 !!a⟶P′
      ... | inj₂ (μ≡τ , _) = impossible !!a⟶P′ μ≡τ
      ... | inj₁ (P″ , !a⟶P″ , P′∼!!a∣P″) with 6-1-3-2 !a⟶P″
      ...   | inj₂ (μ≡τ , _) = impossible !!a⟶P′ μ≡τ
      ...   | inj₁ (.∅ , action , P″∼!a∣∅) =
          _
        , (! a ·      [ name a ]⟶⟨ replication (par-right action) ⟩
           ! a · ∣ ∅)
        , _
        , (P′            ∼⟨ P′∼!!a∣P″ ⟩
           ! ! a · ∣ P″  ∼⟨ lemma P″∼!a∣∅ ⟩∎
           ! ! a ·)
        , _
        , base
        , (! a ·      ∼⟨ symmetric ∣-right-identity ⟩∎
           ! a · ∣ ∅)

      rl : ∀ {P Q Q′ μ} →
           P R Q → Q [ μ ]⟶ Q′ →
           ∃ λ P′ → P [ μ ]⟶ P′ × (_∼_ ⊙ _R_ ⊙ _∼_) P′ Q′
      rl {Q′ = Q′} base !a⟶Q′ with 6-1-3-2 !a⟶Q′
      ... | inj₂ (refl , .∅ , Q″ , .a , action , a⟶Q″ , _) =
        ⊥-elim (names-are-not-inverted a⟶Q″)
      ... | inj₁ (.∅ , action , Q′∼!a∣∅) =
          _
        , (! ! a ·       [ name a ]⟶⟨ replication (par-right !a⟶Q′) ⟩
           ! ! a · ∣ Q′)
        , _
        , (! ! a · ∣ Q′  ∼⟨ lemma Q′∼!a∣∅ ⟩∎
           ! ! a ·)
        , _
        , base
        , (! a ·      ∼⟨ symmetric ∣-right-identity ⟩
           ! a · ∣ ∅  ∼⟨ symmetric Q′∼!a∣∅ ⟩∎
           Q′)

  ----------------------------------------------------------------------
  -- A result mentioned in "Enhancements of the bisimulation proof
  -- method"

  ·∣·∼·· : ∀ {a} → a · ∣ a · ∼ name a · (a ·)
  ·∣·∼·· {a} =
    _⇔_.to larger⇔smallest (bisimulation-up-to-∪⊆∼ R-is _ _ base)
    where
    data _R_ : Proc → Proc → Set where
      base : (a · ∣ a ·) R (name a · (a ·))

    R-is : Bisimulation-up-to-∪ lzero _R_
    R-is = ⟨ lr , rl ⟩
      where
      lr : ∀ {P P′ Q μ} →
           P R Q → P [ μ ]⟶ P′ →
           ∃ λ Q′ → Q [ μ ]⟶ Q′ × (_R_ ∪ _∼_) P′ Q′
      lr base (par-left action) =
          _
        , (name a · (a ·)  [ name a ]⟶⟨ action ⟩
           a ·)
        , inj₂ (∅ ∣ a ·  ∼⟨ ∣-left-identity ⟩∎
                a ·)

      lr base (par-right action) =
          _
        , (name a · (a ·)  [ name a ]⟶⟨ action ⟩
           a ·)
        , inj₂ (a · ∣ ∅  ∼⟨ ∣-right-identity ⟩∎
                a ·)

      lr base (par-τ′ a≡co-a action action) = ⊥-elim (id≢co a≡co-a)

      rl : ∀ {P Q Q′ μ} →
           P R Q → Q [ μ ]⟶ Q′ →
           ∃ λ P′ → P [ μ ]⟶ P′ × (_R_ ∪ _∼_) P′ Q′
      rl base action =
          _
        , (a · ∣ a ·  [ name a ]⟶⟨ par-right action ⟩
           a · ∣ ∅)
        , inj₂ (a · ∣ ∅  ∼⟨ ∣-right-identity ⟩∎
                a ·)