------------------------------------------------------------------------
-- An LTS from Section 6.2.5 of "Enhancements of the bisimulation
-- proof method" by Pous and Sangiorgi
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

open import Prelude

module Labelled-transition-system.6-2-5 (Name : Type) where

open import Labelled-transition-system

infixr 12 _·_
infix   5 _[_]
infix   4 _[_]⟶_

-- Processes.

data Proc : Type where
  op  : Proc → Proc
  _·_ : Name → Proc → Proc
  ∅   : Proc

-- Transitions.

data _[_]⟶_ : Proc → Name → Proc → Type where
  action : ∀ {a P} → a · P [ a ]⟶ P
  op     : ∀ {a P P′ P″} → P [ a ]⟶ P′ → P′ [ a ]⟶ P″ → op P [ a ]⟶ P″

-- The LTS.

6-2-5 : LTS lzero
6-2-5 = record
  { Proc      = Proc
  ; Label     = Name
  ; _[_]⟶_    = _[_]⟶_
  ; is-silent = λ _ → false
  }

open LTS 6-2-5 public hiding (Proc; _[_]⟶_)

-- Polyadic contexts.

data Context (n : ℕ) : Type where
  hole : (x : Fin n) → Context n
  op   : Context n → Context n
  _·_  : (a : Name) → Context n → Context n
  ∅    : Context n

-- Hole filling.

_[_] : ∀ {n} → Context n → (Fin n → Proc) → Proc
hole x [ ps ] = ps x
op C   [ ps ] = op (C [ ps ])
a · C  [ ps ] = a · (C [ ps ])
∅      [ ps ] = ∅
