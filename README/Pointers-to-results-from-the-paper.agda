------------------------------------------------------------------------
-- Pointers to results from the paper
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module README.Pointers-to-results-from-the-paper where

import Bisimilarity.Classical
import Bisimilarity.Coinductive
import Bisimilarity.Coinductive.Delay-monad
import Bisimilarity.Comparison
import Bisimilarity.Exercises.Coinductive.CCS
import Bisimilarity.Step
import Bisimilarity.Up-to
import Bisimilarity.Up-to.CCS
import Bisimilarity.Up-to.Counterexamples
import Bisimilarity.Weak.CCS
import Bisimilarity.Weak.Coinductive.Other
import Bisimilarity.Weak.Delay-monad
import Delay-monad
import Delay-monad.Expansion
import Delay-monad.Strong-bisimilarity
import Delay-monad.Weak-bisimilarity
import Expansion
import Expansion.CCS
import Expansion.Delay-monad
import Indexed-container
import Labelled-transition-system
import Labelled-transition-system.CCS
import Labelled-transition-system.Delay-monad
import Relation
import Similarity.Strong
import Similarity.Strong.CCS
import Up-to

------------------------------------------------------------------------
-- Section 2

-- The Delay monad.

Delay  = Delay-monad.Delay
Delay′ = Delay-monad.∞Delay
never  = Delay-monad.never

-- Strong bisimilarity for the delay monad.

[_]_∼D_     = Delay-monad.Strong-bisimilarity.Strongly-bisimilar
[_]_∼′D_    = Delay-monad.Strong-bisimilarity.∞Strongly-bisimilar
transitiveˢ = Delay-monad.Strong-bisimilarity.transitive

------------------------------------------------------------------------
-- Section 3 and Appendix A

-- Indexed containers.

Container = Indexed-container.Container
⟦_⟧       = Indexed-container.⟦_⟧
map       = Indexed-container.map

-- Index-preserving functions.

_⊆_ = Relation._⊆_

-- The greatest fixpoint.

ν      = Indexed-container.ν
ν′     = Indexed-container.ν′
ν-out  = Indexed-container.ν-out
ν-in   = Indexed-container.ν-in
unfold = Indexed-container.unfold

------------------------------------------------------------------------
-- Section 4

-- Labelled transition systems.
--
-- (The treatment of silent labels differs from that in the paper.)

LTS = Labelled-transition-system.LTS

-- The record type B.
--
-- The type is parametrised so that it can also be used to define weak
-- bisimilarity and expansion.

B-record = Bisimilarity.Step.Step

-- The container B.

B-container = Bisimilarity.Step.S̲t̲e̲p̲

-- The definition of Step in terms of a container is pointwise
-- logically equivalent to the direct definition, and in the presence
-- of extensionality the definitions are pointwise isomorphic.

container-isomorphic-to-record = Bisimilarity.Step.Step↔S̲t̲e̲p̲

-- The traditional definition of bisimilarity.

Bisimilar = Bisimilarity.Classical.[_]_∼_

-- The definition using ν.

[_]_∼_ = Bisimilarity.Coinductive.[_]_∼_

-- The two definitions are pointwise logically equivalent.

classical-and-ν-equivalent =
  Bisimilarity.Comparison.classical⇔coinductive

-- The definition using ν′.

[_]_∼′_ = Bisimilarity.Coinductive.[_]_∼′_

-- Weak transitions.

_[_]⇒̂_ = Labelled-transition-system.LTS._[_]⇒̂_

-- Weak bisimilarity.

[_]_≈_ = Bisimilarity.Weak.Coinductive.Other.[_]_≈_

-- The labelled transition system for the delay monad.

delay-monad-lts = Labelled-transition-system.Delay-monad.delay-monad

-- The definition of bisimilarity obtained from this LTS is pointwise
-- logically equivalent to Strongly-bisimilar.

delay-monad-direct⇔indirect =
  Bisimilarity.Coinductive.Delay-monad.direct⇔indirect

-- Symmetry of bisimilarity for an arbitrary LTS.

symmetric  = Bisimilarity.Coinductive.symmetric-∼
symmetric′ = Bisimilarity.Coinductive.symmetric-∼′

-- Transitivity of bisimilarity for an arbitrary LTS.

transitive = Bisimilarity.Coinductive.transitive-∼

------------------------------------------------------------------------
-- Section 5

-- CCS.

Name-with-kind      = Labelled-transition-system.CCS.Name-with-kind
co                  = Labelled-transition-system.CCS.co
Action              = Labelled-transition-system.CCS.Action
Proc                = Labelled-transition-system.CCS.Proc
Proc′               = Labelled-transition-system.CCS.Proc′
transition-relation = Labelled-transition-system.CCS._[_]⟶_
_∉_                 = Labelled-transition-system.CCS._∉_

-- The constructor ⟨ν_⟩ is called ν, and _·_ is called _·′_. An
-- "inductive" variant of _·′_ is called _·_.

inductive-variant-of-·′ = Labelled-transition-system.CCS._·_

-- Restricted and the corresponding lemma.

Restricted   = Bisimilarity.Exercises.Coinductive.CCS.Restricted
Restricted∼∅ = Bisimilarity.Exercises.Coinductive.CCS.Restricted∼∅

-- ∅ is a left identity for parallel composition.

∅∣ = Bisimilarity.Exercises.Coinductive.CCS.∣-left-identity

-- Proofs showing that all the CCS process constructors preserve
-- strong bisimilarity. (For ∅ the proof is simply reflexivity of
-- strong bisimilarity.)
--
-- The proofs are written in such a way that the arguments can be
-- reused for similar proofs about strong similarity.

module Strong-bisimilarity-congruence where

  _∣-cong_  = Bisimilarity.Exercises.Coinductive.CCS._∣-cong_
  ·-cong    = Bisimilarity.Exercises.Coinductive.CCS._·′-cong_
  !-cong    = Bisimilarity.Exercises.Coinductive.CCS.!-cong_
  _⊕-cong_  = Bisimilarity.Exercises.Coinductive.CCS._⊕-cong_
  ⟨ν_⟩-cong = Bisimilarity.Exercises.Coinductive.CCS.ν-cong
  ∅-cong    = Bisimilarity.Coinductive.reflexive-∼

-- The example with P and Q.

P   = Bisimilarity.Exercises.Coinductive.CCS.Another-example.P
Q   = Bisimilarity.Exercises.Coinductive.CCS.Another-example.Q
P∼Q = Bisimilarity.Exercises.Coinductive.CCS.Another-example.P∼Q

-- The code uses overloaded equational reasoning combinators.

import Equational-reasoning
import Bisimilarity.Coinductive.Equational-reasoning-instances

-- Equations of the form [ ∞ ] P ∼ (C [ P ]) have unique solutions for
-- contexts C where every hole is under a prefix.

unique-solutions-for-weakly-guarded-contexts =
  Bisimilarity.Exercises.Coinductive.CCS.6-2-16

------------------------------------------------------------------------
-- Section 6

-- Up-to techniques.

Up-to = Up-to.Up-to-technique

-- Relation transformers.

Trans = Relation.Trans

-- Size-preserving transformers.

Size-preserving = Up-to.Size-preserving

-- Composition of binary relations.

_⊙_ = Relation._⊙_

-- Up to bisimilarity.

Up-to-bisimilarity = Bisimilarity.Up-to.Up-to-bisimilarity
up-to-bisimilarity-size-preserving =
  Bisimilarity.Up-to.Up-to-bisimilarity-size-preserving

-- Up to context.

Up-to-context                 = Bisimilarity.Up-to.CCS.Up-to-context
up-to-context-size-preserving =
  Bisimilarity.Up-to.CCS.Up-to-context-size-preserving

-- Up to the simple context consisting of replication applied to a
-- single hole.

Up-to-!                 = Bisimilarity.Up-to.CCS.Up-to-!-context
up-to-!-size-preserving =
  Bisimilarity.Up-to.CCS.Up-to-!-context-size-preserving

-- Size-preserving transformers are up-to techniques.

size-preserving⇒up-to = Up-to.size-preserving→up-to

-- There are monotone (and extensive) up-to techniques G and H such
-- that G ∘ H is not an up-to-technique.

not-closed-under-composition =
  Bisimilarity.Up-to.Counterexamples.∃[monotone×extensive×up-to]²×¬∘-up-to

-- Size-preserving is closed under composition.

∘-closure = Up-to.∘-closure

-- There is a (monotone and extensive) up-to technique that is not
-- size-preserving.

not-size-preserving =
  Bisimilarity.Up-to.Counterexamples.∃monotone×extensive×up-to×¬size-preserving

-- Monotonicity.

Monotone = Relation.Monotone

-- The definition of Size-preserving can be simplified for monotone
-- transformers.

simplification = Up-to.monotone→⇔

-- There is a size-preserving transformer that is not monotone (and
-- not extensive either).

not-monotone =
  Bisimilarity.Up-to.Counterexamples.∃size-preserving×¬[monotone⊎extensive]

-- There is a transformer that, despite preserving every approximation
-- of the greatest fixpoint of some container, is not an up-to
-- technique for this container.

not-up-to =
  Bisimilarity.Up-to.Counterexamples.∃special-case-of-size-preserving×¬up-to

------------------------------------------------------------------------
-- Section 7

-- The companion.

Companion = Up-to.Companion

-- Transformers below the companion.

Below-the-companion = Up-to.Below-the-companion

-- Transformers are below the companion if and only if they are
-- size-preserving.

below-the-companion⇔size-preserving = Up-to.⊆companion⇔size-preserving

-- The companion is size-preserving.

companion-size-preserving = Up-to.companion-size-preserving

-- Compatibility.

Compatible = Up-to.Compatible

-- The large companion.

Companion₁ = Up-to.Companion′

-- Monotone and compatible transformers are size-preserving.

compatible⇒size‐preserving = Up-to.monotone→compatible→size-preserving

-- The large companion is below the small one.

large⊆small = Up-to.companion′⊆companion

-- The small companion is monotone.

companion-monotone = Up-to.companion-monotone

-- The small companion is compatible if and only if it is below the
-- large one.

small-compatible⇔⊆large =
  Up-to.companion-compatible⇔companion⊆companion′

-- Various properties of the companion.

id-below                    = Up-to.id⊆companion
⟦⟧-below                    = Up-to.⟦⟧⊆companion
companion∘companion-below   = Up-to.companion²⊆companion
ν⊆companion-⊥,companion-⊥⊆ν = Up-to.ν⇔companion-⊥
companion-up-to             = Up-to.companion-up-to

------------------------------------------------------------------------
-- Section 8

-- Pous and Sangiorgi's lemma 6.1.3, part (2).

6-1-3-2 = Bisimilarity.Exercises.Coinductive.CCS.6-1-3-2

-- The primed variant of _∣-cong_.

_∣-cong′_ = Bisimilarity.Exercises.Coinductive.CCS._∣-cong′_

-- Replication preserves strong bisimilarity (already mentioned
-- above).
--
-- As mentioned above the proof is written in such a way that the
-- argument can be reused for a similar proof about strong similarity.

!-cong₂ = Bisimilarity.Exercises.Coinductive.CCS.!-cong_

-- Proofs showing that all the CCS process constructors preserve
-- strong bisimilarity (already mentioned above).

module Strong-bisimilarity-congruence₂ = Strong-bisimilarity-congruence

-- Proofs showing that all the CCS process constructors preserve
-- strong similarity. (For ∅ the proof is simply reflexivity.)

module Strong-similarity-congruence where

  _∣-cong_  = Similarity.Strong.CCS._∣-cong_
  ·-cong    = Similarity.Strong.CCS._·′-cong_
  !-cong    = Similarity.Strong.CCS.!-cong_
  _⊕-cong_  = Similarity.Strong.CCS._⊕-cong_
  ⟨ν_⟩-cong = Similarity.Strong.CCS.ν-cong
  ∅-cong    = Similarity.Strong.reflexive-≤

-- Proofs showing that all the CCS process constructors, except for
-- sum, preserve the expansion relation. (For ∅ the proof is simply
-- reflexivity.)

module Expansion-almost-congruence where

  _∣-cong_  = Expansion.CCS._∣-cong_
  ·-cong    = Expansion.CCS._·′-cong_
  !-cong    = Expansion.CCS.!-cong_
  ⟨ν_⟩-cong = Expansion.CCS.ν-cong
  ∅-cong    = Expansion.reflexive-≳

-- Proofs showing that all the CCS process constructors, except for
-- sum, preserve weak bisimilarity. (For ∅ the proof is simply
-- reflexivity.)

module Weak-bisimilarity-almost-congruence where

  _∣-cong_  = Bisimilarity.Weak.CCS._∣-cong_
  ·-cong    = Bisimilarity.Weak.CCS._·′-cong_
  !-cong    = Bisimilarity.Weak.CCS.!-cong_
  ⟨ν_⟩-cong = Bisimilarity.Weak.CCS.ν-cong
  ∅-cong    = Bisimilarity.Weak.Coinductive.Other.reflexive-≈

------------------------------------------------------------------------
-- Section 9

-- Weak bisimilarity for the delay monad.

[_]_≈D_  = Delay-monad.Weak-bisimilarity.Weakly-bisimilar
[_]_≈′D_ = Delay-monad.Weak-bisimilarity.∞Weakly-bisimilar

-- This definition is pointwise logically equivalent, in a
-- size-preserving way, to the one obtained from the LTS for the delay
-- monad.

direct⇔indirect = Bisimilarity.Weak.Delay-monad.direct⇔indirect

-- Capretta's definition of weak bisimilarity, formulated using sized
-- types.

Capretta's-weak-bisimilarity =
  Delay-monad.Weak-bisimilarity.Weakly-bisimilar″

-- Capretta's definition is pointwise logically equivalent, in a
-- size-preserving way, to the one used in the paper.

direct⇔Capretta =
  Delay-monad.Weak-bisimilarity.Weakly-bisimilar⇔Weakly-bisimilar″

-- The later constructors can be removed.

laterʳ⁻¹ = Delay-monad.Weak-bisimilarity.laterʳ⁻¹
laterˡ⁻¹ = Delay-monad.Weak-bisimilarity.laterˡ⁻¹
later⁻¹  = Delay-monad.Weak-bisimilarity.later⁻¹

-- Weak bisimilarity is transitive for every LTS.

transitiveʷ-lts = Bisimilarity.Weak.Coinductive.Other.transitive-≈

-- Weak bisimilarity for the delay monad is transitive.

transitiveʷ-now   = Delay-monad.Weak-bisimilarity.⇓-respects-≈
transitiveʷ-later = Delay-monad.Weak-bisimilarity.later-trans
transitiveʷ       = Delay-monad.Weak-bisimilarity.transitive

-- Transitivity cannot be made size-preserving.

Drop-later            = Delay-monad.Weak-bisimilarity.Laterˡ⁻¹-∼≈
now≉never             = Delay-monad.Weak-bisimilarity.now≉never
basic-counterexample  =
  Delay-monad.Weak-bisimilarity.size-preserving-laterˡ⁻¹-∼≈⇔uninhabited
symmetryˢ             = Delay-monad.Strong-bisimilarity.symmetric
symmetryʷ             = Delay-monad.Weak-bisimilarity.symmetric
not-size-preservingʷˢ =
  Delay-monad.Weak-bisimilarity.size-preserving-transitivity-≈∼ʳ⇔uninhabited
not-size-preservingˢʷ =
  Delay-monad.Weak-bisimilarity.size-preserving-transitivity-∼≈ˡ⇔uninhabited
strong-to-weak        = Delay-monad.Weak-bisimilarity.∼→≈
not-size-preservingʷʳ =
  Delay-monad.Weak-bisimilarity.size-preserving-transitivityʳ⇔uninhabited
not-size-preservingʷˡ =
  Delay-monad.Weak-bisimilarity.size-preserving-transitivityˡ⇔uninhabited
trivial               = Delay-monad.Weak-bisimilarity.uninhabited→trivial

-- Size-preserving transitivity-like proofs involving strong
-- bisimilarity.

transitiveˢʷ = Delay-monad.Weak-bisimilarity.transitive-∼≈
transitiveʷˢ = Delay-monad.Weak-bisimilarity.transitive-≈∼

-- The expansion relation.

[_]_≳D_ = Delay-monad.Expansion.Expansion

-- Size-preserving transitivity-like proofs involving the expansion
-- relation.

transitiveᵉ  = Delay-monad.Expansion.transitive
transitiveᵉʷ = Delay-monad.Expansion.transitive-≳≈
transitiveʷᵉ = Delay-monad.Expansion.transitive-≈≲

-- The expansion relation, defined for any LTS.

[_]_≳_ = Expansion.[_]_≳_

-- The explicit definition of expansion for the delay monad is
-- pointwise logically equivalent, in a size-preserving way, to the
-- one obtained from the LTS for the delay monad.

direct⇔indirect-expansion = Expansion.Delay-monad.direct⇔indirect

-- Size-preserving transitivity-like proofs involving the expansion
-- relation for an arbitrary LTS.

transitiveᵉ-lts  = Expansion.transitive-≳
transitiveᵉʷ-lts = Bisimilarity.Weak.Coinductive.Other.transitive-≳≈
transitiveʷᵉ-lts = Bisimilarity.Weak.Coinductive.Other.transitive-≈≲

-- Negative results related to the expansion relation.

not-size-preservingˢᵉ =
  Delay-monad.Expansion.size-preserving-transitivity-∼≳ˡ⇔uninhabited
not-size-preservingᵉʷ =
  Delay-monad.Expansion.size-preserving-transitivity-≳≈ˡ⇔uninhabited
not-size-preservingʷᵉ =
  Delay-monad.Expansion.size-preserving-transitivity-≈≳ˡ⇔uninhabited
