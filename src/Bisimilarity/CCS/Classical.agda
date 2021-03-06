------------------------------------------------------------------------
-- Lemmas related to bisimilarity and CCS, implemented using the
-- classical definition of bisimilarity
------------------------------------------------------------------------

{-# OPTIONS --sized-types #-}

open import Prelude

module Bisimilarity.CCS.Classical {ℓ} {Name : Type ℓ} where

open import Equality.Propositional
open import Logical-equivalence using (_⇔_)
open import Prelude.Size

import Bisimilarity.CCS.General
import Bisimilarity.Classical.Equational-reasoning-instances
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
  data R : Rel₂ ℓ (Proc ∞) where
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
  data S : Rel₂ ℓ (Proc ∞) where
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
  data R : Rel₂ ℓ (Proc ∞) where
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
P∼P′ ∣-cong Q∼Q′ with _⇔_.to (Bisimilarity↔ _) P∼P′
                    | _⇔_.to (Bisimilarity↔ _) Q∼Q′
... | L , L-bisim , PLP′
    | R , R-bisim , QRQ′ = ⟨ LR , ⟪ lr , rl ⟫ , base PLP′ QRQ′ ⟩
  where
  data LR : Rel₂ ℓ (Proc ∞) where
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
-- Exercise 6.1.2 from "Enhancements of the bisimulation proof method"
-- by Pous and Sangiorgi

6-1-2 : ∀ {P} → ! P ∣ P ∼ ! P
6-1-2 {P} = ⟨ R , R-is-a-bisimulation , base ⟩
  where
  data R : Rel₂ ℓ (Proc ∞) where
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
-- Exercise 6.1.3 (2) from "Enhancements of the bisimulation proof
-- method" by Pous and Sangiorgi

open Bisimilarity.CCS.General.6-1-3-2 (record
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
