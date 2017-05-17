------------------------------------------------------------------------
-- Experiments related to bisimilarity
--
-- Nils Anders Danielsson
------------------------------------------------------------------------

module README where

-- Overloaded "equational" reasoning combinators.

import Equational-reasoning

-- Unary and binary relations.

import Relation

-- Indexed containers.

import Indexed-container

-- Container combinators.

import Indexed-container.Combinators

-- Up-to techniques.

import Up-to

-- Closure properties for Compatible and Size-preserving.

import Up-to.Closure

------------------------------------------------------------------------
-- Labelled transition systems

-- Labelled transition systems (LTSs).

import Labelled-transition-system
import Labelled-transition-system.Equational-reasoning-instances

-- CCS.

import Labelled-transition-system.CCS

-- A labelled transition system for the delay monad.

import Labelled-transition-system.Delay-monad

-- An LTS from Section 6.2.5 of "Enhancements of the bisimulation
-- proof method" by Pous and Sangiorgi.

import Labelled-transition-system.6-2-5

------------------------------------------------------------------------
-- Similarity

-- The one-sided Step function, used to define similarity and the
-- two-sided step function.

import Similarity.Step

-- A parametrised coinductive definition that can be used to define
-- various forms of similarity.

import Similarity.General

------------------------------------------------------------------------
-- Strong bisimilarity

-- The Step function, used to define strong and weak bisimilarity as
-- well as expansion.

import Bisimilarity.Step

-- The classical definition of (strong) bisimilarity.

import Bisimilarity.Classical
import Bisimilarity.Classical.Equational-reasoning-instances

-- A parametrised coinductive definition that can be used to define
-- strong and weak bisimilarity as well as expansion.

import Bisimilarity.Coinductive.General

-- A coinductive definition of (strong) bisimilarity.

import Bisimilarity.Coinductive
import Bisimilarity.Coinductive.Equational-reasoning-instances

-- A comparison of the two definitions of bisimilarity.

import Bisimilarity.Comparison

-- Some results related to strong bisimilarity for the delay monad.

import Bisimilarity.Coinductive.Delay-monad

-- Some exercises and results from "Enhancements of the bisimulation
-- proof method" by Pous and Sangiorgi, as well as other results.

import Bisimilarity.Exercises.Other.CCS
import Bisimilarity.Exercises.Classical.CCS
import Bisimilarity.Exercises.Coinductive.CCS
import Bisimilarity.Exercises.Coinductive.6-2-5

-- Up-to techniques.

import Bisimilarity.Up-to
import Bisimilarity.Up-to.CCS
import Bisimilarity.Up-to.Counterexamples

------------------------------------------------------------------------
-- Expansion

-- A coinductive definition of the expansion ordering.

import Expansion
import Expansion.Equational-reasoning-instances

-- Lemmas related to expansion and CCS.

import Expansion.CCS

-- Some results related to expansion for the delay monad.

import Expansion.Delay-monad

------------------------------------------------------------------------
-- Weak bisimilarity

-- A classical definition of weak bisimilarity.

import Bisimilarity.Weak.Classical

-- A coinductive definition of weak bisimilarity.

import Bisimilarity.Weak.Coinductive
import Bisimilarity.Weak.Coinductive.Equational-reasoning-instances

-- Another coinductive definition of weak bisimilarity.

import Bisimilarity.Weak.Coinductive.Other
import
  Bisimilarity.Weak.Coinductive.Other.Equational-reasoning-instances

-- A comparison of the classical definition of weak bisimilarity and
-- one of the coinductive ones.

import Bisimilarity.Weak.Comparison

-- The two coinductive definitions of weak bisimilarity are logically
-- equivalent.

import Bisimilarity.Weak.Coinductive.Equivalent

-- Lemmas related to weak bisimilarity and CCS.

import Bisimilarity.Weak.CCS

-- An example related to CCS from "Enhancements of the bisimulation
-- proof method" by Pous and Sangiorgi.

import Bisimilarity.Weak.CCS.Example

-- Some results about various forms of coinductively defined weak
-- bisimilarity for the delay monad.

import Bisimilarity.Weak.Delay-monad

-- Up-to techniques.

import Bisimilarity.Weak.Coinductive.Other.Up-to
import Bisimilarity.Weak.Coinductive.Other.Up-to.CCS
import Bisimilarity.Weak.Coinductive.Up-to.Delay-monad
