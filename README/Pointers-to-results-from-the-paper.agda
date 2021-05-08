------------------------------------------------------------------------
-- Pointers to results from the paper
------------------------------------------------------------------------

-- Note that the code has evolved after the paper was published. For
-- code that is closer to the paper, see the version of the code that
-- is distributed with the paper.

{-# OPTIONS --sized-types #-}

module README.Pointers-to-results-from-the-paper where

import Bisimilarity
import Bisimilarity.CCS
import Bisimilarity.Classical
import Bisimilarity.Comparison
import Bisimilarity.Delay-monad
import Bisimilarity.Equational-reasoning-instances
import Bisimilarity.CCS.Examples
import Bisimilarity.CCS.Examples.Natural-numbers
import Bisimilarity.Step
import Bisimilarity.Up-to
import Bisimilarity.Up-to.CCS
import Bisimilarity.Up-to.Counterexamples
import Bisimilarity.Weak
import Bisimilarity.Weak.CCS
import Bisimilarity.Weak.Delay-monad
import Bisimilarity.Weak.Up-to
import Delay-monad
import Delay-monad.Bisimilarity
import Delay-monad.Bisimilarity.Alternative
import Delay-monad.Bisimilarity.Negative
import Expansion
import Expansion.CCS
import Expansion.Delay-monad
import Indexed-container
import Indexed-container.Delay-monad
import Labelled-transition-system
import Labelled-transition-system.CCS
import Labelled-transition-system.Delay-monad
import Relation
import Similarity
import Similarity.CCS
import Up-to
import Up-to.Closure

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
--
-- Note that, unlike in the paper, strong bisimilarity, weak
-- bisimilarity and the expansion relation are defined as a single
-- family (with an extra index).

[_]_∼D_  = Delay-monad.Bisimilarity.[_]_∼_
[_]_∼′D_ = Delay-monad.Bisimilarity.[_]_∼′_

-- Strong bisimilarity is transitive.
--
-- (The proof is more general than the one in the paper.)

transitiveˢ = Delay-monad.Bisimilarity.transitive-∼ʳ

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

[_]_∼_ = Bisimilarity.[_]_∼_

-- The two definitions are pointwise logically equivalent.

classical-and-ν-equivalent =
  Bisimilarity.Comparison.classical⇔coinductive

-- The definition using ν′.

[_]_∼′_ = Bisimilarity.[_]_∼′_

-- Derived transition relations.

_⇒_    = Labelled-transition-system.LTS._⇒_
_[_]⇒_ = Labelled-transition-system.LTS._[_]⇒_
_[_]⇒̂_ = Labelled-transition-system.LTS._[_]⇒̂_
_[_]→̂_ = Labelled-transition-system.LTS._[_]⟶̂_

-- Weak bisimilarity.

[_]_≈_ = Bisimilarity.Weak.[_]_≈_

-- Expansion.

[_]_≳_ = Expansion.[_]_≳_

-- A general definition that can be instantiated with different
-- transition relations to yield strong or weak bisimilarity or the
-- expansion relation.

import Bisimilarity.General

-- The labelled transition system for the delay monad.

delay-monad-lts = Labelled-transition-system.Delay-monad.delay-monad

-- The definition of bisimilarity obtained from this LTS is pointwise
-- logically equivalent to the direct definition of strong
-- bisimilarity for the delay monad.

delay-monad-direct⇔indirect = Bisimilarity.Delay-monad.direct⇔indirect

-- Symmetry of bisimilarity for an arbitrary LTS.
--
-- Note that, due to the use of a container in the definition of
-- strong bisimilarity, the proof uses a helper function instead of
-- the copatterns left-to-right and right-to-left. Furthermore the
-- function map₃ is not used, but rather a combination of other
-- functions. Similar remarks apply to several definitions below.

symmetric  = Bisimilarity.symmetric-∼
symmetric′ = Bisimilarity.symmetric-∼′

-- Transitivity of bisimilarity for an arbitrary LTS.

transitive = Bisimilarity.transitive-∼

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

-- The transition relation takes finite processes to finite processes.

finite→finite = Labelled-transition-system.CCS.finite→finite

-- Restricted and the corresponding lemma.

Restricted   = Bisimilarity.CCS.Examples.Restricted
Restricted∼∅ = Bisimilarity.CCS.Examples.Restricted∼∅

-- ∅ is a left identity for parallel composition.

∣-left-identity = Bisimilarity.CCS.∣-left-identity

-- Proofs showing that all the CCS process constructors preserve
-- strong bisimilarity. (For ∅ the proof is simply reflexivity of
-- strong bisimilarity.)
--
-- The proofs are written in such a way that the arguments can be
-- reused for similar proofs about strong similarity. (See below for
-- proofs that are closer to the proofs in the paper.)

module Strong-bisimilarity-congruence where

  _∣-cong_  = Bisimilarity.CCS._∣-cong_
  ·-cong    = Bisimilarity.CCS._·-cong_
  !-cong    = Bisimilarity.CCS.!-cong_
  _⊕-cong_  = Bisimilarity.CCS._⊕-cong_
  ⟨ν_⟩-cong = Bisimilarity.CCS.⟨ν_⟩-cong
  ∅-cong    = Bisimilarity.reflexive-∼

-- Some proofs have been repeated in order to provide code which is
-- closer to that presented in the paper.

module As-in-the-paper where

  _∣-cong_ = Bisimilarity.CCS._∣-congP_
  ·-cong   = Bisimilarity.CCS.·-congP
  !-cong   = Bisimilarity.CCS.!-congP

-- The code uses overloaded equational reasoning combinators.

import Equational-reasoning

-- The proof As-in-the-paper._∣-cong_ does not use symmetric′, but the
-- overloaded combinator symmetric. Agda resolves this use of
-- symmetric to an instance corresponding to symmetric′.

symmetric′-instance =
  Bisimilarity.Equational-reasoning-instances.symmetric∼′

-- Lemmas corresponding to ·-cong for expansion and weak bisimilarity.

module ·-cong where

  expansion         = Expansion.CCS._·-cong_
  weak-bisimilarity = Bisimilarity.Weak.CCS._·-cong_

-- The example with P and Q.

P   = Bisimilarity.CCS.Examples.Natural-numbers.P
Q   = Bisimilarity.CCS.Examples.Natural-numbers.Q
P∼Q = Bisimilarity.CCS.Examples.Natural-numbers.P∼Q

-- The processes in the family P are irregular.

P-irregular = Bisimilarity.CCS.Examples.Natural-numbers.P-irregular

-- The combinators _■ and _∼⟨_⟩_ presented in the paper correspond to
-- two instances.

_■     = Bisimilarity.Equational-reasoning-instances.reflexive∼
_∼⟨_⟩_ = Bisimilarity.Equational-reasoning-instances.trans∼∼

-- Equations of the form [ ∞ ] P ∼ (C [ P ]) have unique solutions up
-- to bisimilarity for contexts C where every hole is under a prefix.

existence  = Bisimilarity.CCS.solutions-exist
uniqueness = Bisimilarity.CCS.unique-solutions

------------------------------------------------------------------------
-- Section 6

-- Up-to techniques.

Up-to-technique = Up-to.Up-to-technique

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

-- If a transformer is size-preserving, then it satisfies a
-- corresponding property for ν′ (and vice versa).

size-preserving′ = Up-to.size-preserving⇔size-preserving′

-- Size-preserving transformers are up-to techniques.

size-preserving→up-to = Up-to.size-preserving→up-to

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

-- There are monotone (and extensive) up-to techniques G and H such
-- that G ∘ H is not an up-to-technique.

not-closed-under-composition =
  Bisimilarity.Up-to.Counterexamples.∃[monotone×extensive×up-to]²×¬∘-up-to

-- Size-preserving is closed under composition.

∘-closure = Up-to.∘-closure

-- It is not the case that every (monotone and extensive) up-to
-- technique is size-preserving.

¬up-to→size-preserving =
  Bisimilarity.Up-to.Counterexamples.¬monotone×extensive×up-to→size-preserving

-- There are at least two up-to techniques that are not
-- size-preserving (despite being monotone and extensive).

not-size-preserving =
  Bisimilarity.Up-to.Counterexamples.∃monotone×extensive×up-to×¬size-preserving

-- Monotone and compatible transformers are up-to techniques.

monotone→compatible→up-to = Up-to.monotone→compatible→up-to

-- If F is monotone and symmetric, and compatible for strong
-- similarity for some LTS, then F is compatible for strong
-- bisimilarity for this LTS.

compatible-for-similarity→compatible-for-bisimilarity =
  Up-to.Closure.compatible-for-similarity→compatible-for-bisimilarity

-- It is not in general the case that if F is monotone and symmetric,
-- and size-preserving for strong similarity for some LTS, then F is
-- size-preserving for strong bisimilarity for this LTS.

¬-compatible-for-similarity→compatible-for-bisimilarity =
  Up-to.Closure.¬-Size-preserving-⟷/⊗

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

companion₁⊆companion = Up-to.companion₁⊆companion

-- The small companion is monotone.

companion-monotone = Up-to.companion-monotone

-- The small companion is compatible if and only if it is below the
-- large one.

companion-compatible⇔companion⊆companion₁ =
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

6-1-3-2 = Bisimilarity.CCS.6-1-3-2

-- Instances corresponding to some equational reasoning combinators
-- mentioned in the paper.

_∼′⟨_⟩′_ = Bisimilarity.Equational-reasoning-instances.trans∼′∼′
_∼⟨_⟩′_  = Bisimilarity.Equational-reasoning-instances.trans∼∼′
_■′      = Bisimilarity.Equational-reasoning-instances.reflexive∼′

-- The primed variant of _∣-cong_.

_∣-cong′_ = Bisimilarity.CCS._∣-cong′_

-- Replication preserves strong bisimilarity (already mentioned
-- above).

!-cong₂ = Bisimilarity.CCS.!-congP

-- Proofs showing that all the CCS process constructors preserve
-- strong bisimilarity (already mentioned above).

module Strong-bisimilarity-congruence₂ = Strong-bisimilarity-congruence

-- Proofs showing that all the CCS process constructors preserve
-- strong similarity. (For ∅ the proof is simply reflexivity.)

module Strong-similarity-congruence where

  _∣-cong_  = Similarity.CCS._∣-cong_
  ·-cong    = Similarity.CCS._·-cong_
  !-cong    = Similarity.CCS.!-cong_
  _⊕-cong_  = Similarity.CCS._⊕-cong_
  ⟨ν_⟩-cong = Similarity.CCS.⟨ν_⟩-cong
  ∅-cong    = Similarity.reflexive-≤

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
  ∅-cong    = Bisimilarity.Weak.reflexive-≈

------------------------------------------------------------------------
-- Section 9

-- Weak bisimilarity for the delay monad.
--
-- Note that, unlike in the paper, strong bisimilarity, weak
-- bisimilarity and the expansion relation are defined as a single
-- family (with an extra index).

[_]_≈D_  = Delay-monad.Bisimilarity.[_]_≈_
[_]_≈′D_ = Delay-monad.Bisimilarity.[_]_≈′_

-- This definition is pointwise logically equivalent, in a
-- size-preserving way, to the one obtained from the LTS for the delay
-- monad.

direct⇔indirect = Bisimilarity.Weak.Delay-monad.direct⇔indirect

-- Capretta's definition of weak bisimilarity, formulated using sized
-- types.

Capretta's-weak-bisimilarity =
  Delay-monad.Bisimilarity.Alternative.[_]_≈₃_

-- Capretta's definition is pointwise logically equivalent, in a
-- size-preserving way, to the one used in the paper.

direct⇔Capretta = Delay-monad.Bisimilarity.Alternative.≈⇔≈₃

------------------------------------------------------------------------
-- Section 9.1

-- Weak bisimilarity is transitive for every LTS.

transitiveʷ-lts = Bisimilarity.Weak.transitive-≈

-- The later constructors can be removed.
--
-- (Two of the proofs are more general than the corresponding proofs
-- in the paper.)

laterʳ⁻¹ = Delay-monad.Bisimilarity.laterʳ⁻¹
laterˡ⁻¹ = Delay-monad.Bisimilarity.laterˡ⁻¹
later⁻¹  = Delay-monad.Bisimilarity.later⁻¹

-- Weak bisimilarity for the delay monad is transitive.
--
-- (The proof is not quite identical to the one in the paper.)

transitiveʷ-now   = Delay-monad.Bisimilarity.transitive-≈-now
transitiveʷ-later = Delay-monad.Bisimilarity.transitive-≈-later
transitiveʷ       = Delay-monad.Bisimilarity.transitive-≈

------------------------------------------------------------------------
-- Section 9.2

-- If transitivity of weak bisimilarity for the delay monad is
-- size-preserving in both arguments, then weak bisimilarity is
-- trivial.

size-preserving→trivial =
  Delay-monad.Bisimilarity.Negative.size-preserving-transitivity-≈→trivial

-- Weak bisimilarity for the delay monad is reflexive.

_∎ʷ = Delay-monad.Bisimilarity.reflexive

-- The computation now x is not weakly bisimilar to never.
--
-- (The proof is more general than the one in the paper.)

now≉never = Delay-monad.Bisimilarity.now≉never

-- If transitivity of weak bisimilarity for the delay monad is
-- size-preserving in both arguments, then the carrier type is
-- uninhabited.

not-size-preservingʷ =
  Delay-monad.Bisimilarity.Negative.size-preserving-transitivity-≈→uninhabited

-- If transitivity of weak bisimilarity is size-preserving in the
-- first argument, then weak bisimulations up to weak bisimilarity are
-- contained in weak bisimilarity.

size-preserving→weak-bisimulations-up-to-weak-bisimilarity-works =
  Bisimilarity.Weak.Up-to.size-preserving-transitivity→up-to-weak-bisimilarity-up-to

-- The Drop-later predicate.

Drop-later = Delay-monad.Bisimilarity.Negative.Laterˡ⁻¹-∼≈

-- Drop-later A implies that A is not inhabited, and vice versa.
--
-- The implementation of basic-counterexample in the paper is
-- different, because it does not include the "and vice versa" part.

basic-counterexample =
  Delay-monad.Bisimilarity.Negative.size-preserving-laterˡ⁻¹-∼≈⇔uninhabited

-- If there is a transitivity-like proof that takes a fully defined
-- weak bisimilarity proof and a strong bisimilarity proof of size i
-- to a weak bisimilarity proof of size i, then the carrier type is
-- uninhabited (and vice versa).
--
-- The implementation is superficially different from the one in the
-- paper (except for the "vice versa" part, which is not present in
-- the paper).

not-size-preservingʷˢ =
  Delay-monad.Bisimilarity.Negative.size-preserving-transitivity-≈∼ʳ⇔uninhabited

-- A size-preserving translation from strong to weak bisimilarity for
-- the delay monad.
--
-- (The implementation is more general than the one in the paper.)

strong-to-weak = Delay-monad.Bisimilarity.∼→

-- Size-preserving translations from strong bisimilarity to expansion
-- and from expansion to weak bisimilarity for any LTS.

strong-to-expansion = Expansion.∼⇒≳
expansion-to-weak   = Bisimilarity.Weak.≳⇒≈

-- If there is a proof of transitivity that takes a fully defined weak
-- bisimilarity proof and a weak bisimilarity proof of size i to a
-- weak bisimilarity proof of size i, then the carrier type is
-- uninhabited (and vice versa).
--
-- The implementation is superficially different from the one in the
-- paper (except for the "vice versa" part, which is not present in
-- the paper).

not-size-preservingʷʳ =
  Delay-monad.Bisimilarity.Negative.size-preserving-transitivity-≈ʳ⇔uninhabited

-- Size-preserving symmetry proofs for strong and weak bisimilarity.
--
-- (Actually a single proof that works for both relations.)

symmetryˢ = Delay-monad.Bisimilarity.symmetric
symmetryʷ = Delay-monad.Bisimilarity.symmetric

-- If there is a proof of transitivity that takes a strong (or
-- alternatively weak) bisimilarity proof of size i and a fully
-- defined weak bisimilarity proof to a weak bisimilarity proof of
-- size i, then the carrier type is uninhabited (and vice versa).

not-size-preservingˢʷ =
  Delay-monad.Bisimilarity.Negative.size-preserving-transitivity-∼≈ˡ⇔uninhabited
not-size-preservingʷˡ =
  Delay-monad.Bisimilarity.Negative.size-preserving-transitivity-≈ˡ⇔uninhabited

-- If the carrier type is not inhabited, then weak bisimilarity is
-- trivial.
--
-- (The proof is more general than the one in the paper.)

trivial = Delay-monad.Bisimilarity.uninhabited→trivial

-- If the type A is uninhabited, then Drop-later A is inhabited (and
-- vice versa).

basic-counterexample′ =
  Delay-monad.Bisimilarity.Negative.size-preserving-laterˡ⁻¹-∼≈⇔uninhabited

-- If the carrier type is uninhabited, then there is a fully
-- size-preserving transitivity proof for weak bisimilarity (and vice
-- versa).

size-preservingʷ =
  Delay-monad.Bisimilarity.Negative.size-preserving-transitivity-≈⇔uninhabited

-- Size-preserving transitivity-like proofs involving strong and weak
-- bisimilarity.
--
-- (The type signatures of the proofs are more general than those
-- given in the paper.)

transitiveˢʷ = Delay-monad.Bisimilarity.transitive-∼ˡ
transitiveʷˢ = Delay-monad.Bisimilarity.transitive-∞∼ʳ

-- A direct definition of expansion for the delay monad.

[_]_≳D_ = Delay-monad.Bisimilarity.[_]_≳_

-- The direct definition of expansion for the delay monad is pointwise
-- logically equivalent, in a size-preserving way, to the one obtained
-- from the LTS for the delay monad.

direct⇔indirect-expansion = Expansion.Delay-monad.direct⇔indirect

-- Size-preserving transitivity-like proofs involving the direct
-- definitions of weak bisimilarity and expansion for the delay monad.
--
-- (The type signatures of the first three proofs are more general
-- than those given in the paper.)

transitiveᵉˢ = Delay-monad.Bisimilarity.transitive-∼ʳ
transitiveᵉ  = Delay-monad.Bisimilarity.transitive-≳ˡ
transitiveᵉʷ = Delay-monad.Bisimilarity.transitive-≳ˡ
transitiveʷᵉ = Delay-monad.Bisimilarity.transitive-≈≲

-- Size-preserving transitivity-like proofs involving weak
-- bisimilarity and expansion defined for an arbitrary LTS.

transitiveᵉˢ-lts = Expansion.transitive-≳∼
transitiveᵉ-lts  = Expansion.transitive-≳
transitiveᵉʷ-lts = Bisimilarity.Weak.transitive-≳≈
transitiveʷᵉ-lts = Bisimilarity.Weak.transitive-≈≲

-- Negative results related to expansion.

not-size-preservingˢᵉ =
  Delay-monad.Bisimilarity.Negative.size-preserving-transitivity-∼≳ˡ⇔uninhabited
not-size-preservingᵉʷ =
  Delay-monad.Bisimilarity.Negative.size-preserving-transitivity-≳≈ˡ⇔uninhabited
not-size-preservingʷᵉ =
  Delay-monad.Bisimilarity.Negative.size-preserving-transitivity-≈≳ˡ⇔uninhabited

-- The functions transitiveᵉ, transitiveᵉʷ and transitiveʷᵉ cannot in
-- general be made fully size-preserving.

not-fully-size-preservingᵉ =
  Delay-monad.Bisimilarity.Negative.size-preserving-transitivity-≳⇔uninhabited
not-fully-size-preservingᵉʷ =
  Delay-monad.Bisimilarity.Negative.size-preserving-transitivity-≳≈⇔uninhabited
not-fully-size-preservingʷᵉ =
  Delay-monad.Bisimilarity.Negative.size-preserving-transitivity-≈≲⇔uninhabited

-- Up to expansion.

Up-to-expansion =
  Bisimilarity.Weak.Up-to.Up-to-expansion
up-to-expansion-size-preserving =
  Bisimilarity.Weak.Up-to.up-to-expansion-size-preserving

-- Relations that satisfy the diagrams of the variant of up to
-- expansion where two occurrences of the expansion relation have been
-- replaced by weak bisimilarity are contained in weak bisimilarity.

variant-of-up-to-expansion = Bisimilarity.Weak.Up-to.6-5-2-4
