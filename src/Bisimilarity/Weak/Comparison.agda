------------------------------------------------------------------------
-- A comparison of the classical definition of weak bisimilarity and
-- one of the coinductive ones
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Bisimilarity.Weak.Comparison where

open import Equality.Propositional
open import Logical-equivalence using (_⇔_)
open import Prelude

open import H-level equality-with-J
open import Surjection equality-with-J using (_↠_)
open import Univalence-axiom equality-with-J

import Bisimilarity.Classical
import Bisimilarity.Coinductive
import Bisimilarity.Comparison as Comp
import Bisimilarity.Weak.Classical
import Bisimilarity.Weak.Coinductive
open import Labelled-transition-system

module _ {lts : LTS} where

  open LTS lts

  private
    module Cl = Bisimilarity.Weak.Classical   lts
    module Co = Bisimilarity.Weak.Coinductive lts

  -- Classically weakly bisimilar processes are coinductively weakly
  -- bisimilar.

  cl⇒co : ∀ {ℓ i p q} → Cl.[ ℓ ] p ≈ q → Co.[ i ] p ≈ q
  cl⇒co = Comp.cl⇒co

  -- Coinductively weakly bisimilar processes are classically weakly
  -- bisimilar.

  co⇒cl : ∀ {ℓ p q} → p Co.≈ q → Cl.[ ℓ ] p ≈ q
  co⇒cl = Comp.co⇒cl

  -- The function cl⇒co is a left inverse of co⇒cl (up to pointwise
  -- bisimilarity).

  cl⇒co∘co⇒cl : ∀ {ℓ i p q}
                (p≈q : p Co.≈ q) →
                Co.[ i ] cl⇒co (co⇒cl {ℓ = ℓ} p≈q) ≡ p≈q
  cl⇒co∘co⇒cl = Comp.cl⇒co∘co⇒cl

  -- If there are two processes that are not equal, but weakly
  -- bisimilar, then co⇒cl is not a left inverse of cl⇒co.

  co⇒cl∘cl⇒co : ∀ {p q ℓ} →
                p ≢ q → p Co.≈ q →
                ∃ λ (p≈p : Cl.[ ℓ ] p ≈ p) → co⇒cl (cl⇒co p≈p) ≢ p≈p
  co⇒cl∘cl⇒co = Comp.co⇒cl∘cl⇒co

  -- The two definitions of weak bisimilarity are logically
  -- equivalent.

  classical⇔coinductive :
    ∀ {ℓ p q} → Cl.[ ℓ ] p ≈ q ⇔ p Co.≈ q
  classical⇔coinductive = Comp.classical⇔coinductive

  -- The larger classical versions of weak bisimilarity are logically
  -- equivalent to the smallest one.

  larger⇔smallest : ∀ {ℓ p q} → Cl.[ ℓ ] p ≈ q ⇔ p Cl.≈ q
  larger⇔smallest = Comp.larger⇔smallest

  -- There is a split surjection from the classical definition of
  -- bisimilarity to the coinductive one (assuming two kinds of
  -- extensionality).

  classical↠coinductive :
    Extensionality lzero lzero →
    Co.Extensionality →
    ∀ {ℓ p q} → Cl.[ ℓ ] p ≈ q ↠ p Co.≈ q
  classical↠coinductive = Comp.classical↠coinductive

-- There is at least one LTS for which there is a split surjection
-- from the coinductive definition of weak bisimilarity to the
-- classical one.

coinductive↠classical :
  ∀ {ℓ p q} →
  Bisimilarity.Weak.Coinductive._≈_  empty   p q ↠
  Bisimilarity.Weak.Classical.[_]_≈_ empty ℓ p q
coinductive↠classical {p = ()}

-- There is an LTS for which coinductive weak bisimilarity is
-- pointwise propositional (assuming two kinds of extensionality and
-- univalence).

coinductive-weak-bisimilarity-is-sometimes-propositional :
  Extensionality lzero (lsuc lzero) →
  Univalence lzero →
  let module Co = Bisimilarity.Weak.Coinductive one-loop in
  Co.Extensionality → Is-proposition (tt Co.≈ tt)
coinductive-weak-bisimilarity-is-sometimes-propositional ext univ =
  subst (λ lts → let module Co = Bisimilarity.Coinductive lts in
                  ∀ p → Co.Extensionality → Is-proposition (p Co.∼ p))
        (sym $ weak≡id ext univ one-loop (λ _ ()))
        (λ _ → Comp.coinductive-bisimilarity-is-sometimes-propositional
                 (lower-extensionality _ _ ext))
        _

-- However, classical weak bisimilarity is, for the same LTS, not
-- pointwise propositional (assuming extensionality and univalence).

classical-weak-bisimilarity-is-not-propositional :
  Extensionality lzero (lsuc lzero) →
  Univalence lzero →
  let module Cl = Bisimilarity.Weak.Classical one-loop in
  ∀ {ℓ} → ¬ Is-proposition (Cl.[ ℓ ] tt ≈ tt)
classical-weak-bisimilarity-is-not-propositional ext univ {ℓ} =
  subst (λ lts → let module Cl = Bisimilarity.Classical lts in
                 ∀ p → ¬ Is-proposition (Cl.[ ℓ ] p ∼ p))
        (sym $ weak≡id ext univ one-loop (λ _ ()))
        (λ _ → Comp.classical-bisimilarity-is-not-propositional)
        _

-- Thus there is, in general, no split surjection from the coinductive
-- definition of weak bisimilarity to the classical one (assuming two
-- kinds of extensionality and univalence).

¬coinductive↠classical :
  Extensionality lzero (lsuc lzero) →
  Univalence lzero →
  ∀ {ℓ} →
  Bisimilarity.Weak.Coinductive.Extensionality one-loop →
  ¬ (∀ {p q} → Bisimilarity.Weak.Coinductive._≈_  one-loop   p q ↠
               Bisimilarity.Weak.Classical.[_]_≈_ one-loop ℓ p q)
¬coinductive↠classical ext univ {ℓ} =
  subst (λ lts → Bisimilarity.Coinductive.Extensionality lts →
                 ¬ (∀ {p q} → Bisimilarity.Coinductive._∼_  lts   p q ↠
                              Bisimilarity.Classical.[_]_∼_ lts ℓ p q))
        (sym $ weak≡id ext univ one-loop (λ _ ()))
        (Comp.¬coinductive↠classical (lower-extensionality _ _ ext))

-- Note also that coinductive weak bisimilarity is not always
-- propositional (assuming extensionality and univalence).

coinductive-weak-bisimilarity-is-not-propositional :
  Extensionality lzero (lsuc lzero) →
  Univalence lzero →
  let open Bisimilarity.Weak.Coinductive two-bisimilar-processes in
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
  Extensionality lzero (lsuc lzero) →
  Univalence lzero →
  {A : Set} →
  let open Bisimilarity.Weak.Coinductive (bisimilarity⇔equality A) in
  {p q : A} → p ≈ q ↠ p ≡ q
weak-bisimilarity↠equality ext univ {A} =
  subst (λ lts → let open Bisimilarity.Coinductive lts in
                 ∀ {p q} → p ∼ q ↠ p ≡ q)
        (sym $ weak≡id ext univ (bisimilarity⇔equality A) (λ _ ()))
        Comp.bisimilarity↠equality
