------------------------------------------------------------------------
-- Experiments related to bisimilarity
--
-- Nils Anders Danielsson
------------------------------------------------------------------------

module Read-me where

-- Overloaded "equational" reasoning combinators.

import Equational-reasoning

-- Labelled transition systems.

import Labelled-transition-system

------------------------------------------------------------------------
-- Strong bisimilarity

-- The classical definition of (strong) bisimilarity.

import Bisimilarity.Classical.Preliminaries
import Bisimilarity.Classical

-- A coinductive definition of (strong) bisimilarity.

import Bisimilarity.Coinductive
import Bisimilarity.Coinductive.Equational-reasoning-instances

-- A comparison of the two definitions of bisimilarity.

import Bisimilarity.Comparison

-- Some exercises and results from "Enhancements of the bisimulation
-- proof method" by Pous and Sangiorgi.

import Bisimilarity.Exercises.Other
import Bisimilarity.Exercises.Classical
import Bisimilarity.Exercises.Coinductive

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
