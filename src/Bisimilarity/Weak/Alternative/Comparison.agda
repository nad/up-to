------------------------------------------------------------------------
-- A comparison of the two alternative definitions of weak
-- bisimilarity
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Bisimilarity.Weak.Alternative.Comparison where

open import Equality.Propositional
open import Logical-equivalence using (_⇔_)
open import Prelude

open import H-level equality-with-J
open import Surjection equality-with-J using (_↠_)
open import Univalence-axiom equality-with-J

import Bisimilarity.Classical
import Bisimilarity.Coinductive
import Bisimilarity.Comparison as Comp
import Bisimilarity.Weak.Alternative
import Bisimilarity.Weak.Alternative.Classical
open import Labelled-transition-system

module _ {ℓ} {lts : LTS ℓ} where

  open LTS lts

  private
    module Co = Bisimilarity.Weak.Alternative           lts
    module Cl = Bisimilarity.Weak.Alternative.Classical lts

  -- Classically weakly bisimilar processes are coinductively weakly
  -- bisimilar.

  cl⇒co : ∀ {i p q} → p Cl.≈ q → Co.[ i ] p ≈ q
  cl⇒co = Comp.cl⇒co

  -- Coinductively weakly bisimilar processes are classically weakly
  -- bisimilar.

  co⇒cl : ∀ {p q} → p Co.≈ q → p Cl.≈ q
  co⇒cl = Comp.co⇒cl

  -- The function cl⇒co is a left inverse of co⇒cl (up to pointwise
  -- bisimilarity).

  cl⇒co∘co⇒cl : ∀ {i p q}
                (p≈q : p Co.≈ q) →
                Co.[ i ] cl⇒co (co⇒cl p≈q) ≡ p≈q
  cl⇒co∘co⇒cl = Comp.cl⇒co∘co⇒cl

  -- If there are two processes that are not equal, but weakly
  -- bisimilar, then co⇒cl is not a left inverse of cl⇒co.

  co⇒cl∘cl⇒co : ∀ {p q} →
                p ≢ q → p Co.≈ q →
                ∃ λ (p≈p : p Cl.≈ p) → co⇒cl (cl⇒co p≈p) ≢ p≈p
  co⇒cl∘cl⇒co = Comp.co⇒cl∘cl⇒co

  -- The two definitions of weak bisimilarity are logically
  -- equivalent.

  classical⇔coinductive : ∀ {p q} → p Cl.≈ q ⇔ p Co.≈ q
  classical⇔coinductive = Comp.classical⇔coinductive

  -- There is a split surjection from the classical definition of
  -- bisimilarity to the coinductive one (assuming two kinds of
  -- extensionality).

  classical↠coinductive :
    Extensionality ℓ ℓ →
    Co.Extensionality →
    ∀ {p q} → p Cl.≈ q ↠ p Co.≈ q
  classical↠coinductive = Comp.classical↠coinductive

-- There is at least one LTS for which there is a split surjection
-- from the coinductive definition of weak bisimilarity to the
-- classical one.

coinductive↠classical :
  ∀ {p q} →
  Bisimilarity.Weak.Alternative._≈_           empty p q ↠
  Bisimilarity.Weak.Alternative.Classical._≈_ empty p q
coinductive↠classical {p = ()}

-- There is an LTS for which coinductive weak bisimilarity is
-- pointwise propositional (assuming two kinds of extensionality and
-- univalence).

coinductive-weak-bisimilarity-is-sometimes-propositional :
  Extensionality lzero (lsuc lzero) →
  Univalence lzero →
  let module Co = Bisimilarity.Weak.Alternative one-loop in
  Co.Extensionality → Is-proposition (tt Co.≈ tt)
coinductive-weak-bisimilarity-is-sometimes-propositional ext univ =
  subst (λ lts → let module Co = Bisimilarity.Coinductive lts in
                  ∀ p → Co.Extensionality → Is-proposition (p Co.∼ p))
        (sym $ weak≡id ext univ one-loop (λ _ ()))
        (λ _ → Comp.coinductive-bisimilarity-is-sometimes-propositional
                 (lower-extensionality _ _ ext))
        _

-- However, classical weak bisimilarity (of any size) is, for the same
-- LTS, not pointwise propositional (assuming extensionality and
-- univalence).

classical-weak-bisimilarity-is-not-propositional :
  Extensionality lzero (lsuc lzero) →
  Univalence lzero →
  let module Cl = Bisimilarity.Weak.Alternative.Classical one-loop in
  ∀ {ℓ} → ¬ Is-proposition (Cl.Weak-bisimilarity′ ℓ (tt , tt))
classical-weak-bisimilarity-is-not-propositional ext univ {ℓ} =
  subst (λ lts → let module Cl = Bisimilarity.Classical lts in
                 ∀ p → ¬ Is-proposition (Cl.Bisimilarity′ ℓ (p , p)))
        (sym $ weak≡id ext univ one-loop (λ _ ()))
        (λ _ → Comp.classical-bisimilarity-is-not-propositional)
        _

-- Thus, assuming two kinds of extensionality and univalence, there is
-- in general no split surjection from the coinductive definition of
-- weak bisimilarity to the classical one (of any size).

¬coinductive↠classical :
  Extensionality lzero (lsuc lzero) →
  Univalence lzero →
  Bisimilarity.Weak.Alternative.Extensionality one-loop →
  ∀ {ℓ} →
  ¬ (∀ {p q} →
     Bisimilarity.Weak.Alternative._≈_ one-loop p q ↠
     Bisimilarity.Weak.Alternative.Classical.Weak-bisimilarity′
       one-loop ℓ (p , q))
¬coinductive↠classical ext univ ext′ {ℓ} =
  subst (λ lts → Bisimilarity.Coinductive.Extensionality lts →
                 ¬ (∀ {p q} → Bisimilarity.Coinductive._∼_ lts p q ↠
                              Bisimilarity.Classical.Bisimilarity′
                                lts ℓ (p , q)))
        (sym $ weak≡id ext univ one-loop (λ _ ()))
        (λ ext′ → Comp.¬coinductive↠classical
                    (lower-extensionality _ _ ext) ext′)
        ext′

-- Note also that coinductive weak bisimilarity is not always
-- propositional (assuming extensionality and univalence).

coinductive-weak-bisimilarity-is-not-propositional :
  Extensionality lzero (lsuc lzero) →
  Univalence lzero →
  let open Bisimilarity.Weak.Alternative two-bisimilar-processes in
  ¬ (∀ {p q} → Is-proposition (p ≈ q))
coinductive-weak-bisimilarity-is-not-propositional ext univ =
  subst (λ lts → let open Bisimilarity.Coinductive lts in
                 ¬ (∀ {p q} → Is-proposition (p ∼ q)))
        (sym $ weak≡id ext univ two-bisimilar-processes (λ _ ()))
        Comp.coinductive-bisimilarity-is-not-propositional

-- In fact, for every type A there is a pointwise split surjection
-- from a certain instance of weak bisimilarity to equality on A
-- (assuming extensionality and univalence).

weak-bisimilarity↠equality :
  ∀ {a} →
  Extensionality a (lsuc a) →
  Univalence a →
  {A : Set a} →
  let open Bisimilarity.Weak.Alternative (bisimilarity⇔equality A) in
  {p q : A} → p ≈ q ↠ p ≡ q
weak-bisimilarity↠equality ext univ {A} =
  subst (λ lts → let open Bisimilarity.Coinductive lts in
                 ∀ {p q} → p ∼ q ↠ p ≡ q)
        (sym $ weak≡id ext univ (bisimilarity⇔equality A) (λ _ ()))
        (Comp.bisimilarity↠equality {A = A})
