------------------------------------------------------------------------
-- Experiments related to bisimilarity
--
-- Nils Anders Danielsson
------------------------------------------------------------------------

module README where

-- Overloaded "equational" reasoning combinators.

import Equational-reasoning

-- Labelled transition systems.

import Labelled-transition-system
import Labelled-transition-system.Equational-reasoning-instances

-- Unary and binary relations.

import Relation

-- Indexed containers.

import Indexed-container

-- Up-to techniques.

import Up-to

------------------------------------------------------------------------
-- Strong bisimilarity

-- The Step function, used to define strong and weak bisimilarity as
-- well as expansion.

import Bisimilarity.Step

-- The classical definition of (strong) bisimilarity.

import Bisimilarity.Classical

-- A parametrised coinductive definition that can be used to define
-- strong and weak bisimilarity as well as expansion.

import Bisimilarity.Coinductive.General

-- A coinductive definition of (strong) bisimilarity.

import Bisimilarity.Coinductive
import Bisimilarity.Coinductive.Equational-reasoning-instances

-- A comparison of the two definitions of bisimilarity.

import Bisimilarity.Comparison

-- Up-to techniques.

import Bisimilarity.Up-to
import Bisimilarity.Up-to.CCS
import Bisimilarity.Up-to.Delay-monad
import Bisimilarity.Up-to.Counterexamples

-- Some exercises and results from "Enhancements of the bisimulation
-- proof method" by Pous and Sangiorgi.

import Bisimilarity.Exercises.Other
import Bisimilarity.Exercises.Classical
import Bisimilarity.Exercises.Coinductive

------------------------------------------------------------------------
-- Expansion

-- A coinductive definition of the expansion ordering.

import Bisimilarity.Coinductive.Expansion
import Bisimilarity.Coinductive.Expansion.Equational-reasoning-instances

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
-- one of the coinductive ones

import Bisimilarity.Weak.Comparison

-- The two coinductive definitions of weak bisimilarity are logically
-- equivalent.

import Bisimilarity.Weak.Coinductive.Equivalent

-- Some exercises and results from "Enhancements of the bisimulation
-- proof method" by Pous and Sangiorgi.

import Bisimilarity.Weak.Exercises.Coinductive

-- Some results about various forms of coinductively defined weak
-- bisimilarity for the delay monad.

import Bisimilarity.Weak.Delay-monad
