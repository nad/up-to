------------------------------------------------------------------------
-- Some exercises and results related to CCS from "Enhancements of the
-- bisimulation proof method" by Pous and Sangiorgi
--
-- Implemented using the classical definition of bisimilarity.
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Bisimilarity.Exercises.Classical.CCS {Name : Set} where

open import Equality.Propositional
open import Logical-equivalence using (_⇔_)
open import Prelude

open import Bijection equality-with-J using (_↔_)

import Bisimilarity.Classical.Equational-reasoning-instances
open import Bisimilarity.Comparison
import Bisimilarity.Exercises.Other.CCS
open import Equational-reasoning
open import Labelled-transition-system.CCS Name
open import Relation

open import Bisimilarity.Classical CCS

------------------------------------------------------------------------
-- Various lemmas related to _∣_

-- _∣_ is commutative.

∣-comm : ∀ {P Q} → P ∣ Q ∼ Q ∣ P
∣-comm = ⟨ R , R-is-a-bisimulation , base ⟩
  where
  data R : Rel₂ (# 0) (Proc ∞) where
    base : ∀ {P Q} → R (P ∣ Q , Q ∣ P)

  R-is-symmetric : ∀ {P Q} → R (P , Q) → R (Q , P)
  R-is-symmetric base = base

  R-is-a-bisimulation : Bisimulation R
  R-is-a-bisimulation =
    ⟪ lr , (λ PRQ tr →
              Σ-map id (Σ-map id R-is-symmetric)
                (lr (R-is-symmetric PRQ) tr)) ⟫
    where
    lr : ∀ {P P′ Q μ} →
         R (P , Q) → P [ μ ]⟶ P′ →
         ∃ λ Q′ → Q [ μ ]⟶ Q′ × R (P′ , Q′)
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
∣-assoc = ⟨ S , S-is-a-bisimulation , base ⟩
  where
  data S : Rel₂ (# 0) (Proc ∞) where
    base : ∀ {P Q R} → S (P ∣ (Q ∣ R) , (P ∣ Q) ∣ R)

  S-is-a-bisimulation : Bisimulation S
  S-is-a-bisimulation = ⟪ lr , rl ⟫
    where
    lr : ∀ {P P′ Q μ} →
         S (P , Q) → P [ μ ]⟶ P′ →
         ∃ λ Q′ → Q [ μ ]⟶ Q′ × S (P′ , Q′)
    lr base (par-left tr)               = _ , par-left (par-left tr)    , base
    lr base (par-right (par-left tr))   = _ , par-left (par-right tr)   , base
    lr base (par-right (par-right tr))  = _ , par-right tr              , base
    lr base (par-right (par-τ tr₁ tr₂)) = _ , par-τ (par-right tr₁) tr₂ , base
    lr base (par-τ tr₁ (par-left tr₂))  = _ , par-left (par-τ tr₁ tr₂)  , base
    lr base (par-τ tr₁ (par-right tr₂)) = _ , par-τ (par-left tr₁) tr₂  , base

    rl : ∀ {P Q Q′ μ} →
         S (P , Q) → Q [ μ ]⟶ Q′ →
         ∃ λ P′ → P [ μ ]⟶ P′ × S (P′ , Q′)
    rl base (par-left (par-left tr))    = _ , par-left tr               , base
    rl base (par-left (par-right tr))   = _ , par-right (par-left tr)   , base
    rl base (par-left (par-τ tr₁ tr₂))  = _ , par-τ tr₁ (par-left tr₂)  , base
    rl base (par-right tr)              = _ , par-right (par-right tr)  , base
    rl base (par-τ (par-left tr₁) tr₂)  = _ , par-τ tr₁ (par-right tr₂) , base
    rl base (par-τ (par-right tr₁) tr₂) = _ , par-right (par-τ tr₁ tr₂) , base

-- ∅ is a left identity of _∣_.

∣-left-identity : ∀ {P} → ∅ ∣ P ∼ P
∣-left-identity = ⟨ R , R-is-a-bisimulation , base ⟩
  where
  data R : Rel₂ (# 0) (Proc ∞) where
    base : ∀ {P} → R (∅ ∣ P , P)

  R-is-a-bisimulation : Bisimulation R
  R-is-a-bisimulation = ⟪ lr , rl ⟫
    where
    lr : ∀ {P P′ Q μ} →
         R (P , Q) → P [ μ ]⟶ P′ →
         ∃ λ Q′ → Q [ μ ]⟶ Q′ × R (P′ , Q′)
    lr base (par-right tr) = _ , tr , base
    lr base (par-left ())
    lr base (par-τ () _)

    rl : ∀ {P Q Q′ μ} →
         R (P , Q) → Q [ μ ]⟶ Q′ →
         ∃ λ P′ → P [ μ ]⟶ P′ × R (P′ , Q′)
    rl base tr = _ , par-right tr , base

-- ∅ is a right identity of _∣_.

∣-right-identity : ∀ {P} → P ∣ ∅ ∼ P
∣-right-identity {P} =
  P ∣ ∅  ∼⟨ ∣-comm ⟩
  ∅ ∣ P  ∼⟨ ∣-left-identity ⟩■
  P

-- _∣_ preserves bisimilarity.

_∣-cong_ : ∀ {P P′ Q Q′} → P ∼ P′ → Q ∼ Q′ → P ∣ Q ∼ P′ ∣ Q′
P∼P′ ∣-cong Q∼Q′ with _↔_.to Bisimilarity↔ P∼P′
                    | _↔_.to Bisimilarity↔ Q∼Q′
... | L , L-bisim , PLP′
    | R , R-bisim , QRQ′ = ⟨ LR , ⟪ lr , rl ⟫ , base PLP′ QRQ′ ⟩
  where
  data LR : Rel₂ (# 0) (Proc ∞) where
    base : ∀ {P P′ Q Q′} →
           L (P , P′) → R (Q , Q′) → LR (P ∣ Q , P′ ∣ Q′)

  lr : ∀ {P P′ Q μ} →
       LR (P , Q) → P [ μ ]⟶ P′ →
       ∃ λ Q′ → Q [ μ ]⟶ Q′ × LR (P′ , Q′)
  lr (base PLP′ QRQ′) (par-left tr) =
    Σ-map (_∣ _) (Σ-map par-left (flip base QRQ′))
      (left-to-right L-bisim PLP′ tr)

  lr (base PLP′ QRQ′) (par-right tr) =
    Σ-map (_ ∣_) (Σ-map par-right (base PLP′))
      (left-to-right R-bisim QRQ′ tr)

  lr (base PLP′ QRQ′) (par-τ tr₁ tr₂) =
    Σ-zip _∣_ (Σ-zip par-τ base)
      (left-to-right L-bisim PLP′ tr₁)
      (left-to-right R-bisim QRQ′ tr₂)

  rl : ∀ {P Q Q′ μ} →
       LR (P , Q) → Q [ μ ]⟶ Q′ →
       ∃ λ P′ → P [ μ ]⟶ P′ × LR (P′ , Q′)
  rl (base PLP′ QRQ′) (par-left tr) =
    Σ-map (_∣ _) (Σ-map par-left (flip base QRQ′))
      (right-to-left L-bisim PLP′ tr)

  rl (base PLP′ QRQ′) (par-right tr) =
    Σ-map (_ ∣_) (Σ-map par-right (base PLP′))
      (right-to-left R-bisim QRQ′ tr)

  rl (base PLP′ QRQ′) (par-τ tr₁ tr₂) =
    Σ-zip _∣_ (Σ-zip par-τ base)
      (right-to-left L-bisim PLP′ tr₁)
      (right-to-left R-bisim QRQ′ tr₂)

------------------------------------------------------------------------
-- Exercise 6.1.2

6-1-2 : ∀ {P} → ! P ∣ P ∼ ! P
6-1-2 {P} = ⟨ R , R-is-a-bisimulation , base ⟩
  where
  data R : Rel₂ (# 0) (Proc ∞) where
    base : R (! P ∣ P , ! P)
    refl : ∀ {P} → R (P , P)

  R-is-a-bisimulation : Bisimulation R
  R-is-a-bisimulation = ⟪ lr , rl ⟫
    where
    lr : ∀ {P P′ Q μ} →
         R (P , Q) → P [ μ ]⟶ P′ →
         ∃ λ Q′ → Q [ μ ]⟶ Q′ × R (P′ , Q′)
    lr base tr = _ , replication tr , refl
    lr refl tr = _ , tr             , refl

    rl : ∀ {P Q Q′ μ} →
         R (P , Q) → Q [ μ ]⟶ Q′ →
         ∃ λ P′ → P [ μ ]⟶ P′ × R (P′ , Q′)
    rl base (replication tr) = _ , tr , refl
    rl refl tr               = _ , tr , refl

------------------------------------------------------------------------
-- Exercise 6.1.3 (2)

open Bisimilarity.Exercises.Other.CCS.6-1-3-2 (record
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
       public using (swap-rightmost; 6-1-3-2)

------------------------------------------------------------------------
-- Exercise 6.2.4

6-2-4 : ∀ {a} → ! ! a · ∼ ! a ·
6-2-4 {a} =
  _⇔_.to larger⇔smallest (bisimulation-up-to-∼⊆∼ R-is base)
  where
  data R : Rel₂ (# 0) (Proc ∞) where
    base : R (! ! a · , ! a ·)

  impossible : ∀ {μ P q} {Q : Set q} →
               ! ! a · [ μ ]⟶ P → μ ≡ τ → Q
  impossible {μ} !!a⟶P μ≡τ = ⊥-elim $ name≢τ
    (name a  ≡⟨ !-only (!-only ·-only) !!a⟶P ⟩
     μ       ≡⟨ μ≡τ ⟩∎
     τ       ∎)

  R-is : Bisimulation-up-to-bisimilarity lzero R
  R-is = ⟪ lr , rl ⟫
    where
    lemma = λ {P} P∼!a∣∅ →
      ! ! a · ∣ P            ∼⟨ reflexive ∣-cong P∼!a∣∅ ⟩
      ! ! a · ∣ (! a · ∣ ∅)  ∼⟨ reflexive ∣-cong ∣-right-identity ⟩
      ! ! a · ∣ ! a ·        ∼⟨ 6-1-2 ⟩■
      ! ! a ·

    lr : ∀ {P P′ Q μ} →
         R (P , Q) → P [ μ ]⟶ P′ →
         ∃ λ Q′ → Q [ μ ]⟶ Q′ ×
                  (Bisimilarity _ ⊙ R ⊙ Bisimilarity _) (P′ , Q′)
    lr {P′ = P′} base !!a⟶P′ = case 6-1-3-2 !!a⟶P′ of λ where
      (inj₂ (μ≡τ , _)) → impossible !!a⟶P′ μ≡τ
      (inj₁ (P″ , !a⟶P″ , P′∼!!a∣P″)) → case 6-1-3-2 !a⟶P″ of λ where
        (inj₂ (μ≡τ , _)) → impossible !!a⟶P′ μ≡τ
        (inj₁ (.∅ , action , P″∼!a∣∅)) →
            _
          , (! a ·      [ name a ]⟶⟨ replication (par-right action) ⟩
             ! a · ∣ ∅)
          , _
          , (P′            ∼⟨ P′∼!!a∣P″ ⟩
             ! ! a · ∣ P″  ∼⟨ ∼: lemma P″∼!a∣∅ ⟩■
             ! ! a ·)
          , _
          , base
          , (! a ·      ∼⟨ symmetric ∣-right-identity ⟩■
             ! a · ∣ ∅)

    rl : ∀ {P Q Q′ μ} →
         R (P , Q) → Q [ μ ]⟶ Q′ →
         ∃ λ P′ → P [ μ ]⟶ P′ ×
                  (Bisimilarity _ ⊙ R ⊙ Bisimilarity _) (P′ , Q′)
    rl {Q′ = Q′} base !a⟶Q′ = case 6-1-3-2 !a⟶Q′ of λ where
      (inj₂ (refl , .∅ , Q″ , .a , action , a⟶Q″ , _)) →
        ⊥-elim (names-are-not-inverted a⟶Q″)
      (inj₁ (.∅ , action , Q′∼!a∣∅)) →
          _
        , (! ! a ·       [ name a ]⟶⟨ replication (par-right !a⟶Q′) ⟩
           ! ! a · ∣ Q′)
        , _
        , (! ! a · ∣ Q′  ∼⟨ lemma Q′∼!a∣∅ ⟩■
           ! ! a ·)
        , _
        , base
        , (! a ·      ∼⟨ symmetric ∣-right-identity ⟩
           ! a · ∣ ∅  ∼⟨ symmetric Q′∼!a∣∅ ⟩■
           Q′)

------------------------------------------------------------------------
-- A result mentioned in "Enhancements of the bisimulation proof
-- method"

·∣·∼·· : ∀ {a} → a · ∣ a · ∼ name a · (a ·)
·∣·∼·· {a} =
  _⇔_.to larger⇔smallest (bisimulation-up-to-∪⊆∼ R-is base)
  where
  data R : Rel₂ (# 0) (Proc ∞) where
    base : R (a · ∣ a · , name a · (a ·))

  R-is : Bisimulation-up-to-∪ lzero R
  R-is = ⟪ lr , rl ⟫
    where
    lr : ∀ {P P′ Q μ} →
         R (P , Q) → P [ μ ]⟶ P′ →
         ∃ λ Q′ → Q [ μ ]⟶ Q′ × (R ∪ Bisimilarity _) (P′ , Q′)
    lr base (par-left action) =
        _
      , (name a · (a ·)  [ name a ]⟶⟨ action ⟩
         a ·)
      , inj₂ (∅ ∣ a ·  ∼⟨ ∣-left-identity ⟩■
              a ·)

    lr base (par-right action) =
        _
      , (name a · (a ·)  [ name a ]⟶⟨ action ⟩
         a ·)
      , inj₂ (a · ∣ ∅  ∼⟨ ∣-right-identity ⟩■
              a ·)

    lr base (par-τ′ a≡co-a action action) = ⊥-elim (id≢co a≡co-a)

    rl : ∀ {P Q Q′ μ} →
         R (P , Q) → Q [ μ ]⟶ Q′ →
         ∃ λ P′ → P [ μ ]⟶ P′ × (R ∪ Bisimilarity _) (P′ , Q′)
    rl base action =
        _
      , (a · ∣ a ·  [ name a ]⟶⟨ par-right action ⟩
         a · ∣ ∅)
      , inj₂ (a · ∣ ∅  ∼⟨ ∣-right-identity ⟩■
              a ·)
