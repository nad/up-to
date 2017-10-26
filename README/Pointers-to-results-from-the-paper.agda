------------------------------------------------------------------------
-- Pointers to results from the paper
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module README.Pointers-to-results-from-the-paper where

import Bisimilarity.Classical
import Bisimilarity.Coinductive
import Bisimilarity.Coinductive.Delay-monad
import Bisimilarity.Coinductive.Equational-reasoning-instances
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
import Indexed-container.Delay-monad
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
--
-- Note that, unlike the definition in the paper, this definition is
-- universe-polymorphic. Similar remarks apply to many definitions
-- below as well.

Delay  = Delay-monad.Delay
Delay′ = Delay-monad.Delay′

-- The non-terminating computation never.

never = Delay-monad.never

-- Strong bisimilarity for the delay monad.

[_]_∼D_  = Delay-monad.Strong-bisimilarity.[_]_∼_
[_]_∼′D_ = Delay-monad.Strong-bisimilarity.[_]_∼′_

-- Strong bisimilarity is transitive.

transitiveˢ = Delay-monad.Strong-bisimilarity.transitive

------------------------------------------------------------------------
-- Section 3

-- Indexed containers.
--
-- The paper defines indexed containers with one index type, but this
-- definition uses two.

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

-- Relation containment (_⊆_) is not antisymmetric if the index type
-- is inhabited.

⊆-not-antisymmetric = Relation.⊆-not-antisymmetric

-- The shapes of a container are in pointwise bijective correspondence
-- with the interpretation of the container applied to the constant
-- function yielding the unit type.

Shape↔⟦⟧⊤ = Indexed-container.Shape↔⟦⟧⊤

-- A container corresponding to the Delay monad.

DelayC = Indexed-container.Delay-monad.DelayC

-- A (size-preserving) logical equivalence between the direct
-- definition of the delay monad and the indirect definition using ν
-- and the container DelayC.

Delay⇔νDelayC = Indexed-container.Delay-monad.Delay⇔νDelayC

-- Bisimilarity for ν.

ν-bisimilar = Indexed-container.ν-bisimilar

-- The two components of Delay⇔νDelayC {i = ∞} are inverses up to
-- (strong) bisimilarity.

Delay⇔νDelayC-inverses =
  Indexed-container.Delay-monad.Delay⇔νDelayC-inverses

------------------------------------------------------------------------
-- Section 4

-- Labelled transition systems.

LTS = Labelled-transition-system.LTS

-- The record type B.
--
-- The type is parametrised so that it can also be used to define weak
-- bisimilarity and expansion.

B = Bisimilarity.Step.Step

-- The container B^C, roughly as given in the paper.

B^C = Bisimilarity.Step.StepC′

-- The code mainly uses another definition of B^C, built up from
-- smaller building blocks, and employing a trick to make it easier
-- for Agda to infer implicit arguments.

B^C-code = Bisimilarity.Step.StepC

-- The two definitions of B^C have interpretations that are pointwise
-- logically equivalent, and in the presence of extensionality they
-- are pointwise isomorphic.

B^C-code↔B^C = Bisimilarity.Step.StepC↔StepC′

-- The interpretation of B^C is pointwise logically equivalent to B,
-- and in the presence of extensionality they are pointwise
-- isomorphic.

B↔B^C = Bisimilarity.Step.Step↔StepC′

-- The traditional definition of bisimilarity.

Bisimilar = Bisimilarity.Classical._∼_

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
-- logically equivalent to the direct definition of strong
-- bisimilarity for the delay monad.

delay-monad-direct⇔indirect =
  Bisimilarity.Coinductive.Delay-monad.direct⇔indirect

-- Symmetry of bisimilarity for an arbitrary LTS.
--
-- Note that, due to the use of a container in the definition of
-- strong bisimilarity, the proof uses a helper function instead of
-- the copatterns left-to-right and right-to-left. Furthermore the
-- function map₃ is not used, but rather a combination of other
-- functions. Similar remarks apply to several definitions below.

symmetric  = Bisimilarity.Coinductive.symmetric-∼
symmetric′ = Bisimilarity.Coinductive.symmetric-∼′

-- Transitivity of bisimilarity for an arbitrary LTS.

transitive = Bisimilarity.Coinductive.transitive-∼

------------------------------------------------------------------------
-- Section 5

-- CCS.

Name-with-kind = Labelled-transition-system.CCS.Name-with-kind
co             = Labelled-transition-system.CCS.co
Action         = Labelled-transition-system.CCS.Action
is-silent      = Labelled-transition-system.CCS.is-silent
Proc           = Labelled-transition-system.CCS.Proc
Proc′          = Labelled-transition-system.CCS.Proc′
_[_]→_         = Labelled-transition-system.CCS._[_]⟶_
_∉_            = Labelled-transition-system.CCS._∉_

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
-- reused for similar proofs about strong similarity. (See below for
-- proofs that are closer to the proofs in the paper.)

module Strong-bisimilarity-congruence where

  _∣-cong_  = Bisimilarity.Exercises.Coinductive.CCS._∣-cong_
  ·-cong    = Bisimilarity.Exercises.Coinductive.CCS._·-cong_
  !-cong    = Bisimilarity.Exercises.Coinductive.CCS.!-cong_
  _⊕-cong_  = Bisimilarity.Exercises.Coinductive.CCS._⊕-cong_
  ⟨ν_⟩-cong = Bisimilarity.Exercises.Coinductive.CCS.⟨ν_⟩-cong
  ∅-cong    = Bisimilarity.Coinductive.reflexive-∼

-- Some proofs have been repeated in order to provide code which is
-- closer to that presented in the paper.

module As-in-the-paper where

  _∣-cong_ = Bisimilarity.Exercises.Coinductive.CCS._∣-congP_
  ·-cong   = Bisimilarity.Exercises.Coinductive.CCS.·-congP
  !-cong   = Bisimilarity.Exercises.Coinductive.CCS.!-congP

-- The code uses overloaded equational reasoning combinators.

import Equational-reasoning

-- The proof As-in-the-paper._∣-cong_ does not use symmetric′, but the
-- overloaded combinator symmetric. Agda resolves this use of
-- symmetric to an instance corresponding to symmetric′.

symmetric′-instance =
  Bisimilarity.Coinductive.Equational-reasoning-instances.symmetric∼′

-- The example with P and Q.

P   = Bisimilarity.Exercises.Coinductive.CCS.Another-example.P
Q   = Bisimilarity.Exercises.Coinductive.CCS.Another-example.Q
P∼Q = Bisimilarity.Exercises.Coinductive.CCS.Another-example.P∼Q

-- The combinators _■ and _∼⟨_⟩_ presented in the paper correspond to
-- two instances.

_■ =
  Bisimilarity.Coinductive.Equational-reasoning-instances.reflexive∼
_∼⟨_⟩_ =
  Bisimilarity.Coinductive.Equational-reasoning-instances.trans∼∼

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

Up-to-bisimilarity =
  Bisimilarity.Up-to.Up-to-bisimilarity
up-to-bisimilarity-size-preserving =
  Bisimilarity.Up-to.up-to-bisimilarity-size-preserving

-- Up to context.

Up-to-context                 = Bisimilarity.Up-to.CCS.Up-to-context
up-to-context-size-preserving =
  Bisimilarity.Up-to.CCS.up-to-context-size-preserving

-- Up to the simple context consisting of replication applied to a
-- single hole.

Up-to-!                 = Bisimilarity.Up-to.CCS.Up-to-!
up-to-!-size-preserving = Bisimilarity.Up-to.CCS.up-to-!-size-preserving

-- Size-preserving transformers are up-to techniques.

size-preserving→up-to = Up-to.size-preserving→up-to

-- There are monotone (and extensive) up-to techniques G and H such
-- that G ∘ H is not an up-to-technique.

not-closed-under-composition =
  Bisimilarity.Up-to.Counterexamples.∃[monotone×extensive×up-to]²×¬∘-up-to

-- Size-preserving is closed under composition.

∘-closure = Up-to.∘-closure

-- There are at least two up-to techniques that are not
-- size-preserving (despite being monotone and extensive).

not-size-preserving =
  Bisimilarity.Up-to.Counterexamples.∃monotone×extensive×up-to×¬size-preserving

-- Monotonicity.

Monotone = Relation.Monotone

-- The definition of Size-preserving can be simplified for monotone
-- transformers.

simplification = Up-to.monotone→⇔

-- There are at least two size-preserving relation transformers that
-- are not monotone (or extensive).

not-monotone =
  Bisimilarity.Up-to.Counterexamples.∃-2-size-preserving×¬[monotone⊎extensive]

-- There is a container C such that there are at least two
-- transformers that, despite preserving every approximation of the
-- greatest fixpoint of C, are not up-to techniques with respect to C.

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

below-the-companion⇔size-preserving =
  Up-to.below-the-companion⇔size-preserving

-- The companion is size-preserving.

companion-size-preserving = Up-to.companion-size-preserving

-- Compatibility.

Compatible = Up-to.Compatible

-- The large companion.

Companion₁ = Up-to.Companion₁

-- Monotone and compatible transformers are size-preserving.

compatible→size-preserving = Up-to.monotone→compatible→size-preserving

-- The large companion is below the small one.

large⊆small = Up-to.companion₁⊆companion

-- The small companion is monotone.

companion-monotone = Up-to.companion-monotone

-- The small companion is compatible if and only if it is below the
-- large one.

small-compatible⇔⊆large =
  Up-to.companion-compatible⇔companion⊆companion₁

-- The small companion is compatible if certain assumptions (including
-- a strong version of excluded middle) are satisfied. However, at the
-- time of writing I don't know if these assumptions are consistent
-- with the variant of Agda that is used in this development.

companion-compatible = Up-to.companion-compatible

-- The identity function is below the companion.

id-below = Up-to.id-below

-- The interpretation ⟦ C ⟧ of a container C is below the
-- corresponding companion.

⟦⟧-below = Up-to.⟦⟧-below

-- The companion composed with itself is below the companion.

companion∘companion-below = Up-to.companion∘companion-below

-- An example: If F is below the companion, then ⟦ C ⟧ ∘ F is below
-- Companion ∘ Companion, which is below the companion.

below-the-companion-example = Up-to.below-the-companion-example

-- The greatest fixpoint is pointwise logically equivalent to the
-- companion applied to an empty relation.

ν⊆companion-⊥ = Up-to.ν⇔companion-⊥
companion-⊥⊆ν = Up-to.ν⇔companion-⊥

-- The companion is an up-to technique.

companion-up-to = Up-to.companion-up-to

------------------------------------------------------------------------
-- Section 8

-- Pous and Sangiorgi's lemma 6.1.3, part (2).

6-1-3-2 = Bisimilarity.Exercises.Coinductive.CCS.6-1-3-2

-- Instances corresponding to some equational reasoning combinators
-- mentioned in the paper.

_∼′⟨_⟩′_ =
  Bisimilarity.Coinductive.Equational-reasoning-instances.trans∼′∼′
_∼⟨_⟩′_ =
  Bisimilarity.Coinductive.Equational-reasoning-instances.trans∼∼′
_■′ =
  Bisimilarity.Coinductive.Equational-reasoning-instances.reflexive∼′

-- The primed variant of _∣-cong_.

_∣-cong′_ = Bisimilarity.Exercises.Coinductive.CCS._∣-cong′_

-- Replication preserves strong bisimilarity (already mentioned
-- above).

!-cong₂ = Bisimilarity.Exercises.Coinductive.CCS.!-congP

-- Proofs showing that all the CCS process constructors preserve
-- strong bisimilarity (already mentioned above).

module Strong-bisimilarity-congruence₂ = Strong-bisimilarity-congruence

-- Proofs showing that all the CCS process constructors preserve
-- strong similarity. (For ∅ the proof is simply reflexivity.)

module Strong-similarity-congruence where

  _∣-cong_  = Similarity.Strong.CCS._∣-cong_
  ·-cong    = Similarity.Strong.CCS._·-cong_
  !-cong    = Similarity.Strong.CCS.!-cong_
  _⊕-cong_  = Similarity.Strong.CCS._⊕-cong_
  ⟨ν_⟩-cong = Similarity.Strong.CCS.⟨ν_⟩-cong
  ∅-cong    = Similarity.Strong.reflexive-≤

-- Proofs showing that all the CCS process constructors, except for
-- sum, preserve the expansion relation. (For ∅ the proof is simply
-- reflexivity.)

module Expansion-almost-congruence where

  _∣-cong_  = Expansion.CCS._∣-cong_
  ·-cong    = Expansion.CCS._·-cong_
  !-cong    = Expansion.CCS.!-cong_
  ⟨ν_⟩-cong = Expansion.CCS.⟨ν_⟩-cong
  ∅-cong    = Expansion.reflexive-≳

-- Proofs showing that all the CCS process constructors, except for
-- sum, preserve weak bisimilarity. (For ∅ the proof is simply
-- reflexivity.)

module Weak-bisimilarity-almost-congruence where

  _∣-cong_  = Bisimilarity.Weak.CCS._∣-cong_
  ·-cong    = Bisimilarity.Weak.CCS._·-cong_
  !-cong    = Bisimilarity.Weak.CCS.!-cong_
  ⟨ν_⟩-cong = Bisimilarity.Weak.CCS.⟨ν_⟩-cong
  ∅-cong    = Bisimilarity.Weak.Coinductive.Other.reflexive-≈

------------------------------------------------------------------------
-- Section 9

-- Weak bisimilarity for the delay monad.

[_]_≈D_  = Delay-monad.Weak-bisimilarity.[_]_≈_
[_]_≈′D_ = Delay-monad.Weak-bisimilarity.[_]_≈′_

-- This definition is pointwise logically equivalent, in a
-- size-preserving way, to the one obtained from the LTS for the delay
-- monad.

direct⇔indirect = Bisimilarity.Weak.Delay-monad.direct⇔indirect

-- Capretta's definition of weak bisimilarity, formulated using sized
-- types.

Capretta's-weak-bisimilarity = Delay-monad.Weak-bisimilarity.[_]_≈₃_

-- Capretta's definition is pointwise logically equivalent, in a
-- size-preserving way, to the one used in the paper.

direct⇔Capretta = Delay-monad.Weak-bisimilarity.≈⇔≈₃

------------------------------------------------------------------------
-- Section 9.1

-- Weak bisimilarity is transitive for every LTS.

transitiveʷ-lts = Bisimilarity.Weak.Coinductive.Other.transitive-≈

-- The later constructors can be removed.

laterʳ⁻¹ = Delay-monad.Weak-bisimilarity.laterʳ⁻¹
laterˡ⁻¹ = Delay-monad.Weak-bisimilarity.laterˡ⁻¹
later⁻¹  = Delay-monad.Weak-bisimilarity.later⁻¹

-- Weak bisimilarity for the delay monad is transitive.

transitiveʷ-now   = Delay-monad.Weak-bisimilarity.transitive-now
transitiveʷ-later = Delay-monad.Weak-bisimilarity.transitive-later
transitiveʷ       = Delay-monad.Weak-bisimilarity.transitive

------------------------------------------------------------------------
-- Section 9.2

-- The Drop-later predicate.

Drop-later = Delay-monad.Weak-bisimilarity.Laterˡ⁻¹-∼≈

-- The computation now x is not weakly bisimilar to never.

now≉never = Delay-monad.Weak-bisimilarity.now≉never

-- Drop-later A implies that A is not inhabited, and vice versa.
--
-- The implementation of basic-counterexample in the paper is
-- different, because it does not include the "and vice versa" part.

basic-counterexample =
  Delay-monad.Weak-bisimilarity.size-preserving-laterˡ⁻¹-∼≈⇔uninhabited

-- If there is a transitivity-like proof that takes a fully defined
-- weak bisimilarity proof and a strong bisimilarity proof of size i
-- to a weak bisimilarity proof of size i, then the carrier type is
-- uninhabited (and vice versa).
--
-- The implementation is superficially different from the one in the
-- paper (except for the "vice versa" part, which is not present in
-- the paper).

not-size-preservingʷˢ =
  Delay-monad.Weak-bisimilarity.size-preserving-transitivity-≈∼ʳ⇔uninhabited

-- A size-preserving translation from strong to weak bisimilarity.

strong-to-weak = Delay-monad.Weak-bisimilarity.∼→≈

-- If there is a proof of transitivity that takes a fully defined weak
-- bisimilarity proof and a weak bisimilarity proof of size i to a
-- weak bisimilarity proof of size i, then the carrier type is
-- uninhabited (and vice versa).
--
-- The implementation is superficially different from the one in the
-- paper (except for the "vice versa" part, which is not present in
-- the paper).

not-size-preservingʷʳ =
  Delay-monad.Weak-bisimilarity.size-preserving-transitivityʳ⇔uninhabited

-- Size-preserving symmetry proofs for strong and weak bisimilarity.

symmetryˢ = Delay-monad.Strong-bisimilarity.symmetric
symmetryʷ = Delay-monad.Weak-bisimilarity.symmetric

-- If there is a proof of transitivity that takes a strong (or
-- alternatively weak) bisimilarity proof of size i and a fully
-- defined weak bisimilarity proof to a weak bisimilarity proof of
-- size i, then the carrier type is uninhabited (and vice versa).

not-size-preservingˢʷ =
  Delay-monad.Weak-bisimilarity.size-preserving-transitivity-∼≈ˡ⇔uninhabited
not-size-preservingʷˡ =
  Delay-monad.Weak-bisimilarity.size-preserving-transitivityˡ⇔uninhabited

-- If the carrier type is not inhabited, then weak bisimilarity is
-- trivial.

trivial = Delay-monad.Weak-bisimilarity.uninhabited→trivial

-- If the type A is uninhabited, then Drop-later A is inhabited (and
-- vice versa).

basic-counterexample′ =
  Delay-monad.Weak-bisimilarity.size-preserving-laterˡ⁻¹-∼≈⇔uninhabited

-- If the carrier type is uninhabited, then there is a fully
-- size-preserving transitivity proof for weak bisimilarity (and vice
-- versa).

size-preservingʷ =
  Delay-monad.Weak-bisimilarity.size-preserving-transitivity⇔uninhabited

-- Size-preserving transitivity-like proofs involving strong
-- bisimilarity.

transitiveˢʷ = Delay-monad.Weak-bisimilarity.transitive-∼≈
transitiveʷˢ = Delay-monad.Weak-bisimilarity.transitive-≈∼

-- The expansion relation.

[_]_≳D_ = Delay-monad.Expansion.[_]_≳_

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
