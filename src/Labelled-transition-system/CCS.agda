------------------------------------------------------------------------
-- CCS
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe --sized-types #-}

module Labelled-transition-system.CCS {ℓ} (Name : Set ℓ) where

open import Equality.Propositional
open import Prelude
open import Size

open import Bool equality-with-J
open import Function-universe equality-with-J hiding (id; _∘_)

open import Labelled-transition-system

------------------------------------------------------------------------
-- Fixity declarations

infix  12 _∙
infixr 12 _·_ _∙_
infix  10 !_
infix   8 _⊕_
infix   6 _∣_
infix   5 _[_] _[_]′
infix   4 _[_]⟶_ _∉_

------------------------------------------------------------------------
-- CCS, roughly as defined in "Enhancements of the bisimulation proof
-- method" by Pous and Sangiorgi, with support for corecursive
-- processes (instead of the named process constants presented in
-- "Coinduction All the Way Up" by Pous)

-- Names with kinds: (a , true) stands for "a", and (a , false) stands
-- for "a̅".

Name-with-kind : Set ℓ
Name-with-kind = Name × Bool

-- Turns names of one kind into names of the other kind.

co : Name-with-kind → Name-with-kind
co (a , kind) = a , not kind

-- Actions.

data Action : Set ℓ where
  name : Name-with-kind → Action
  τ    : Action

-- The only silent action is τ.

is-silent : Action → Bool
is-silent (name _) = false
is-silent τ        = true

-- Processes.

mutual

  data Proc (i : Size) : Set ℓ where
    ∅       : Proc i
    _∣_ _⊕_ : Proc i → Proc i → Proc i
    _·_     : Action → Proc′ i → Proc i
    ⟨ν_⟩    : Name → Proc i → Proc i
    !_      : Proc i → Proc i

  record Proc′ (i : Size) : Set ℓ where
    coinductive
    field
      force : {j : Size< i} → Proc j

open Proc′ public

-- An inductive variant of _·_.

_∙_ : ∀ {i} → Action → Proc i → Proc i
μ ∙ P = μ · λ { .force → P }

-- An abbreviation.

_∙ : Name-with-kind → Proc ∞
a ∙ = name a ∙ ∅

-- The predicate a ∉ μ holds if a is not the underlying name of μ (if
-- any).

_∉_ : Name → Action → Set ℓ
a ∉ name (b , _) = ¬ a ≡ b
a ∉ τ            = ↑ ℓ ⊤

-- Transition relation.

data _[_]⟶_ : Proc ∞ → Action → Proc ∞ → Set ℓ where
  par-left    : ∀ {P Q P′ μ} → P [ μ ]⟶ P′ → P ∣ Q [ μ ]⟶ P′ ∣ Q
  par-right   : ∀ {P Q Q′ μ} → Q [ μ ]⟶ Q′ → P ∣ Q [ μ ]⟶ P  ∣ Q′
  par-τ       : ∀ {P P′ Q Q′ a} →
                P [ name a ]⟶ P′ → Q [ name (co a) ]⟶ Q′ →
                P ∣ Q [ τ ]⟶ P′ ∣ Q′
  sum-left    : ∀ {P Q P′ μ} → P [ μ ]⟶ P′ → P ⊕ Q [ μ ]⟶ P′
  sum-right   : ∀ {P Q Q′ μ} → Q [ μ ]⟶ Q′ → P ⊕ Q [ μ ]⟶ Q′
  action      : ∀ {P μ} → μ · P [ μ ]⟶ force P
  restriction : ∀ {P P′ a μ} →
                a ∉ μ → P [ μ ]⟶ P′ → ⟨ν a ⟩ P [ μ ]⟶ ⟨ν a ⟩ P′
  replication : ∀ {P P′ μ} → ! P ∣ P [ μ ]⟶ P′ → ! P [ μ ]⟶ P′

-- The CCS LTS.

CCS : LTS ℓ
CCS = record
  { Proc      = Proc ∞
  ; Label     = Action
  ; _[_]⟶_    = _[_]⟶_
  ; is-silent = is-silent
  }

open LTS CCS public hiding (Proc; _[_]⟶_; is-silent)

------------------------------------------------------------------------
-- Contexts and some related definitions, roughly following
-- "Enhancements of the bisimulation proof method" by Pous and
-- Sangiorgi

mutual

  -- Polyadic contexts.

  data Context (i : Size) (n : ℕ) : Set ℓ where
    hole    : (x : Fin n) → Context i n
    ∅       : Context i n
    _∣_ _⊕_ : Context i n → Context i n → Context i n
    _·_     : (μ : Action) → Context′ i n → Context i n
    ⟨ν_⟩    : (a : Name) → Context i n → Context i n
    !_      : Context i n → Context i n

  record Context′ (i : Size) (n : ℕ) : Set ℓ where
    coinductive
    field
      force : {j : Size< i} → Context j n

open Context′ public

mutual

  -- Hole filling.

  _[_] : ∀ {i n} → Context i n → (Fin n → Proc ∞) → Proc i
  hole x   [ Ps ] = Ps x
  ∅        [ Ps ] = ∅
  C₁ ∣ C₂  [ Ps ] = (C₁ [ Ps ]) ∣ (C₂ [ Ps ])
  C₁ ⊕ C₂  [ Ps ] = (C₁ [ Ps ]) ⊕ (C₂ [ Ps ])
  μ · C    [ Ps ] = μ · (C [ Ps ]′)
  ⟨ν a ⟩ C [ Ps ] = ⟨ν a ⟩ (C [ Ps ])
  ! C      [ Ps ] = ! (C [ Ps ])

  _[_]′ : ∀ {i n} → Context′ i n → (Fin n → Proc ∞) → Proc′ i
  force (C [ Ps ]′) = force C [ Ps ]

-- A context is weakly guarded if every hole is under a prefix (μ ·_).

data Weakly-guarded {n : ℕ} : Context ∞ n → Set ℓ where
  ∅      : Weakly-guarded ∅
  _∣_    : ∀ {C₁ C₂} →
           Weakly-guarded C₁ → Weakly-guarded C₂ →
           Weakly-guarded (C₁ ∣ C₂)
  _⊕_    : ∀ {C₁ C₂} →
           Weakly-guarded C₁ → Weakly-guarded C₂ →
           Weakly-guarded (C₁ ⊕ C₂)
  action : ∀ {μ C} → Weakly-guarded (μ · C)
  ⟨ν⟩    : ∀ {a C} → Weakly-guarded C → Weakly-guarded (⟨ν a ⟩ C)
  !_     : ∀ {C} → Weakly-guarded C → Weakly-guarded (! C)

-- Turns processes into contexts without holes.

context : ∀ {i n} → Proc i → Context i n
context ∅          = ∅
context (P₁ ∣ P₂)  = context P₁ ∣ context P₂
context (P₁ ⊕ P₂)  = context P₁ ⊕ context P₂
context (μ · P)    = μ · λ { .force → context (force P) }
context (⟨ν a ⟩ P) = ⟨ν a ⟩ (context P)
context (! P)      = ! context P

-- Non-degenerate contexts.

mutual

  data Non-degenerate (i : Size) {n : ℕ} : Context ∞ n → Set ℓ where
    hole   : ∀ {x} → Non-degenerate i (hole x)
    ∅      : Non-degenerate i ∅
    _∣_    : ∀ {C₁ C₂} →
             Non-degenerate i C₁ → Non-degenerate i C₂ →
             Non-degenerate i (C₁ ∣ C₂)
    _⊕_    : ∀ {C₁ C₂} →
             Non-degenerate-summand i C₁ →
             Non-degenerate-summand i C₂ →
             Non-degenerate i (C₁ ⊕ C₂)
    action : ∀ {μ C} →
             Non-degenerate′ i (force C) → Non-degenerate i (μ · C)
    ⟨ν⟩    : ∀ {a C} → Non-degenerate i C → Non-degenerate i (⟨ν a ⟩ C)
    !_     : ∀ {C} → Non-degenerate i C → Non-degenerate i (! C)

  data Non-degenerate-summand (i : Size) {n : ℕ} :
                              Context ∞ n → Set ℓ where
    process : ∀ P → Non-degenerate-summand i (context P)
    action  : ∀ {μ C} →
              Non-degenerate′ i (force C) →
              Non-degenerate-summand i (μ · C)

  record Non-degenerate′ (i : Size) {n} (C : Context ∞ n) : Set ℓ where
    coinductive
    field
      force : {j : Size< i} → Non-degenerate j C

open Non-degenerate′ public

------------------------------------------------------------------------
-- Very strong bisimilarity

-- "Very strong" bisimilarity for processes: Equal ∞ P Q means that P
-- and Q have the same structure.

mutual

  data Equal (i : Size) : Proc ∞ → Proc ∞ → Set ℓ where
    ∅    : Equal i ∅ ∅
    _∣_  : ∀ {P₁ P₂ Q₁ Q₂} →
           Equal i P₁ P₂ → Equal i Q₁ Q₂ → Equal i (P₁ ∣ Q₁) (P₂ ∣ Q₂)
    _⊕_  : ∀ {P₁ P₂ Q₁ Q₂} →
           Equal i P₁ P₂ → Equal i Q₁ Q₂ → Equal i (P₁ ⊕ Q₁) (P₂ ⊕ Q₂)
    _·_  : ∀ {μ₁ μ₂ P₁ P₂} →
           μ₁ ≡ μ₂ → Equal′ i (force P₁) (force P₂) →
           Equal i (μ₁ · P₁) (μ₂ · P₂)
    ⟨ν_⟩ : ∀ {a₁ a₂ P₁ P₂} →
           a₁ ≡ a₂ → Equal i P₁ P₂ → Equal i (⟨ν a₁ ⟩ P₁) (⟨ν a₂ ⟩ P₂)
    !_   : ∀ {P₁ P₂} → Equal i P₁ P₂ → Equal i (! P₁) (! P₂)

  record Equal′ (i : Size) (P₁ P₂ : Proc ∞) : Set ℓ where
    coinductive
    field
      force : {j : Size< i} → Equal j P₁ P₂

open Equal′ public

-- Extensionality for very strong bisimilarity.

Proc-extensionality : Set ℓ
Proc-extensionality = ∀ {P Q} → Equal ∞ P Q → P ≡ Q

------------------------------------------------------------------------
-- Some lemmas

-- The co function is involutive.

co-involutive : ∀ a → co (co a) ≡ a
co-involutive (a , kind) =
  (a , not (not kind))  ≡⟨ cong (_ ,_) $ not-involutive kind ⟩∎
  (a , kind)            ∎

-- A name is not equal to the corresponding coname.

id≢co : ∀ {a} → a ≢ co a
id≢co {a} =
  a ≡ co a                 ↝⟨ cong proj₂ ⟩
  proj₂ a ≡ not (proj₂ a)  ↝⟨ not≡⇒≢ _ _ ∘ sym ⟩
  proj₂ a ≢ proj₂ a        ↝⟨ _$ refl ⟩□
  ⊥                        □

-- A cancellation law.

cancel-name : ∀ {a b} → name a ≡ name b → a ≡ b
cancel-name refl = refl

-- A disjointness law.

name≢τ : ∀ {a} → name a ≢ τ
name≢τ ()

-- The only silent label is τ.

silent≡τ : ∀ {μ} → Silent μ → μ ≡ τ
silent≡τ {τ}      _  = refl
silent≡τ {name _} ()

-- Names do not match (the only silent label) τ.

∉τ : ∀ {μ a} → Silent μ → a ∉ μ
∉τ s rewrite silent≡τ s = _

-- A variant of par-τ.

par-τ′ : ∀ {P P′ Q Q′ a b} →
         b ≡ co a → P [ name a ]⟶ P′ → Q [ name b ]⟶ Q′ →
         P ∣ Q [ τ ]⟶ P′ ∣ Q′
par-τ′ refl = par-τ

-- The process μ · P can only make μ-transitions.

·-only : ∀ {μ₁ μ₂ P Q} → μ₁ · P [ μ₂ ]⟶ Q → μ₁ ≡ μ₂
·-only action = refl

-- The process μ · P can only transition to force P.

·-only⟶ : ∀ {μ₁ μ₂ P Q} → μ₁ · P [ μ₂ ]⟶ Q → Q ≡ force P
·-only⟶ action = refl

-- A simple corollary.

names-are-not-inverted :
  ∀ {a P Q} → ¬ (name a · P [ name (co a) ]⟶ Q)
names-are-not-inverted {a} {P} {Q} =
  name a · P [ name (co a) ]⟶ Q  ↝⟨ ·-only ⟩
  name a ≡ name (co a)           ↝⟨ id≢co ∘ cancel-name ⟩□
  ⊥                              □

-- If P₁ and P₂ can only make μ-transitions, then P₁ ∣ P₂ can only
-- make μ-transitions.

∣-only : ∀ {μ₀ P₁ P₂} →
         (∀ {P′ μ} → P₁ [ μ ]⟶ P′ → μ₀ ≡ μ) →
         (∀ {P′ μ} → P₂ [ μ ]⟶ P′ → μ₀ ≡ μ) →
         ∀ {P′ μ} → P₁ ∣ P₂ [ μ ]⟶ P′ → μ₀ ≡ μ
∣-only      only₁ only₂ (par-left tr)           = only₁ tr
∣-only      only₁ only₂ (par-right tr)          = only₂ tr
∣-only {μ₀} only₁ only₂ (par-τ {a = a} tr₁ tr₂) = ⊥-elim (
                                  $⟨ only₁ tr₁ , only₂ tr₂ ⟩
  μ₀ ≡ name a × μ₀ ≡ name (co a)  ↝⟨ uncurry trans ∘ Σ-map sym id ⟩
  name a ≡ name (co a)            ↝⟨ id≢co ∘ cancel-name ⟩□
  ⊥                               □)

-- If P can only make μ-transitions, then ! P can only make
-- μ-transitions.

!-only : ∀ {μ₀ P} →
         (∀ {P′ μ} → P [ μ ]⟶ P′ → μ₀ ≡ μ) →
         ∀ {P′ μ} → ! P [ μ ]⟶ P′ → μ₀ ≡ μ
!-only      only (replication (par-left  tr)) = !-only only tr
!-only      only (replication (par-right tr)) = only tr
!-only {μ₀} only (replication (par-τ {a = a} tr₁ tr₂)) = ⊥-elim (
                                  $⟨ !-only only tr₁ , only tr₂ ⟩
  μ₀ ≡ name a × μ₀ ≡ name (co a)  ↝⟨ uncurry trans ∘ Σ-map sym id ⟩
  name a ≡ name (co a)            ↝⟨ id≢co ∘ cancel-name ⟩□
  ⊥                               □)

-- If P₁ and P₂ can only make μ-transitions, then P₁ ⊕ P₂ can only
-- make μ-transitions.

⊕-only : ∀ {μ₀ P₁ P₂} →
         (∀ {P′ μ} → P₁ [ μ ]⟶ P′ → μ₀ ≡ μ) →
         (∀ {P′ μ} → P₂ [ μ ]⟶ P′ → μ₀ ≡ μ) →
         ∀ {P′ μ} → P₁ ⊕ P₂ [ μ ]⟶ P′ → μ₀ ≡ μ
⊕-only only₁ only₂ (sum-left tr)  = only₁ tr
⊕-only only₁ only₂ (sum-right tr) = only₂ tr

-- If P can only make μ-transitions, then ⟨ν a ⟩ P can only make
-- μ-transitions.

⟨ν⟩-only : ∀ {μ₀ a P} →
           (∀ {P′ μ} → P [ μ ]⟶ P′ → μ₀ ≡ μ) →
           ∀ {P′ μ} → ⟨ν a ⟩ P [ μ ]⟶ P′ → μ₀ ≡ μ
⟨ν⟩-only only (restriction _ tr) = only tr

-- A simple lemma.

·⊕·-co :
  ∀ {a b c P Q R S} →
  name a · P ⊕ name b · Q [ name c ]⟶      R →
  name a · P ⊕ name b · Q [ name (co c) ]⟶ S →
  b ≡ co a × (R ≡ force P × S ≡ force Q ⊎ R ≡ force Q × S ≡ force P)
·⊕·-co (sum-left  action)
       (sum-left  tr)     = ⊥-elim (names-are-not-inverted tr)
·⊕·-co (sum-left  action)
       (sum-right action) = refl , inj₁ (refl , refl)
·⊕·-co (sum-right action)
       (sum-left  action) =   sym (co-involutive _)
                            , inj₂ (refl , refl)
·⊕·-co (sum-right action)
       (sum-right tr)     = ⊥-elim (names-are-not-inverted tr)

-- Very strong bisimilarity is reflexive.

Proc-refl : ∀ {i} P → Equal i P P
Proc-refl ∅          = ∅
Proc-refl (P₁ ∣ P₂)  = Proc-refl P₁ ∣ Proc-refl P₂
Proc-refl (P₁ ⊕ P₂)  = Proc-refl P₁ ⊕ Proc-refl P₂
Proc-refl (μ · P)    = refl · λ { .force → Proc-refl (force P) }
Proc-refl (⟨ν a ⟩ P) = ⟨ν refl ⟩ (Proc-refl P)
Proc-refl (! P)      = ! Proc-refl P

-- Very strong bisimilarity is symmetric.

Proc-sym : ∀ {i P Q} → Equal i P Q → Equal i Q P
Proc-sym ∅          = ∅
Proc-sym (P₁ ∣ P₂)  = Proc-sym P₁ ∣ Proc-sym P₂
Proc-sym (P₁ ⊕ P₂)  = Proc-sym P₁ ⊕ Proc-sym P₂
Proc-sym (p · P)    = sym p · λ { .force → Proc-sym (force P) }
Proc-sym (⟨ν p ⟩ P) = ⟨ν sym p ⟩ (Proc-sym P)
Proc-sym (! P)      = ! Proc-sym P

-- Very strong bisimilarity is transitive.

Proc-trans : ∀ {i P Q R} → Equal i P Q → Equal i Q R → Equal i P R
Proc-trans ∅          ∅          = ∅
Proc-trans (P₁ ∣ P₂)  (Q₁ ∣ Q₂)  = Proc-trans P₁ Q₁ ∣ Proc-trans P₂ Q₂
Proc-trans (P₁ ⊕ P₂)  (Q₁ ⊕ Q₂)  = Proc-trans P₁ Q₁ ⊕ Proc-trans P₂ Q₂
Proc-trans (p · P)    (q · Q)    = trans p q · λ { .force →
                                     Proc-trans (force P) (force Q) }
Proc-trans (⟨ν p ⟩ P) (⟨ν q ⟩ Q) = ⟨ν trans p q ⟩ (Proc-trans P Q)
Proc-trans (! P)      (! Q)      = ! Proc-trans P Q

-- Weakening of contexts.

weaken : ∀ {i n} → Context i n → Context i (suc n)
weaken (hole x)   = hole (fsuc x)
weaken ∅          = ∅
weaken (C₁ ∣ C₂)  = weaken C₁ ∣ weaken C₂
weaken (C₁ ⊕ C₂)  = weaken C₁ ⊕ weaken C₂
weaken (μ · C)    = μ · λ { .force → weaken (force C) }
weaken (⟨ν a ⟩ C) = ⟨ν a ⟩ (weaken C)
weaken (! C)      = ! weaken C

-- A lemma relating weakening and hole filling.

weaken-[] :
  ∀ {i n ps} (C : Context ∞ n) →
  Equal i (weaken C [ ps ]) (C [ ps ∘ fsuc ])
weaken-[] (hole x)   = Proc-refl _
weaken-[] ∅          = ∅
weaken-[] (C₁ ∣ C₂)  = weaken-[] C₁ ∣ weaken-[] C₂
weaken-[] (C₁ ⊕ C₂)  = weaken-[] C₁ ⊕ weaken-[] C₂
weaken-[] (μ · C)    = refl · λ { .force → weaken-[] (force C) }
weaken-[] (⟨ν a ⟩ C) = ⟨ν refl ⟩ (weaken-[] C)
weaken-[] (! C)      = ! weaken-[] C

-- The result of filling the holes in the context "context P" is P.

context-[] : ∀ {i n} {Ps : Fin n → Proc ∞} P →
             Equal i P (context P [ Ps ])
context-[] ∅          = ∅
context-[] (P₁ ∣ P₂)  = context-[] P₁ ∣ context-[] P₂
context-[] (P₁ ⊕ P₂)  = context-[] P₁ ⊕ context-[] P₂
context-[] (μ · P)    = refl · λ { .force → context-[] (force P) }
context-[] (⟨ν a ⟩ P) = ⟨ν refl ⟩ (context-[] P)
context-[] (! P)      = ! (context-[] P)

-- The contexts constructed by the context function are always
-- non-degenerate.

context-non-degenerate :
  ∀ {i n} (P : Proc ∞) → Non-degenerate i (context {n = n} P)
context-non-degenerate ∅          = ∅
context-non-degenerate (P₁ ∣ P₂)  = context-non-degenerate P₁ ∣
                                    context-non-degenerate P₂
context-non-degenerate (P₁ ⊕ P₂)  = process P₁ ⊕ process P₂
context-non-degenerate (μ · P)    = action λ { .force →
                                      context-non-degenerate (force P) }
context-non-degenerate (⟨ν a ⟩ P) = ⟨ν⟩ (context-non-degenerate P)
context-non-degenerate (! P)      = ! context-non-degenerate P

mutual

  -- A relation expressing that a certain process matches a certain
  -- context.

  data Matches (i : Size) {n} : Proc ∞ → Context ∞ n → Set ℓ where
    hole   : ∀ {P} (x : Fin n) → Matches i P (hole x)
    ∅      : Matches i ∅ ∅
    _∣_    : ∀ {P₁ P₂ C₁ C₂} →
             Matches i P₁ C₁ → Matches i P₂ C₂ →
             Matches i (P₁ ∣ P₂) (C₁ ∣ C₂)
    _⊕_    : ∀ {P₁ P₂ C₁ C₂} →
             Matches i P₁ C₁ → Matches i P₂ C₂ →
             Matches i (P₁ ⊕ P₂) (C₁ ⊕ C₂)
    action : ∀ {μ P C} →
             Matches′ i (force P) (force C) →
             Matches i (μ · P) (μ · C)
    ⟨ν⟩    : ∀ {a P C} → Matches i P C → Matches i (⟨ν a ⟩ P) (⟨ν a ⟩ C)
    !_     : ∀ {P C} → Matches i P C → Matches i (! P) (! C)

  record Matches′
           (i : Size) {n} (P : Proc ∞) (C : Context ∞ n) : Set ℓ where
    coinductive
    field
      force : {j : Size< i} → Matches j P C

open Matches′ public

-- The process obtained by filling a context's holes matches the
-- context.

Matches-[] : ∀ {i n Ps} (C : Context ∞ n) → Matches i (C [ Ps ]) C
Matches-[] (hole x)   = hole x
Matches-[] ∅          = ∅
Matches-[] (C₁ ∣ C₂)  = Matches-[] C₁ ∣ Matches-[] C₂
Matches-[] (C₁ ⊕ C₂)  = Matches-[] C₁ ⊕ Matches-[] C₂
Matches-[] (μ · C)    = action λ { .force → Matches-[] (force C) }
Matches-[] (⟨ν a ⟩ C) = ⟨ν⟩ (Matches-[] C)
Matches-[] (! C)      = ! Matches-[] C

-- Matches respects very strong bisimilarity.

Matches-cong : ∀ {i P Q n} {C : Context ∞ n} →
               Equal i P Q → Matches i P C → Matches i Q C
Matches-cong _             (hole x)   = hole x
Matches-cong ∅             ∅          = ∅
Matches-cong (p₁ ∣ p₂)     (q₁ ∣ q₂)  = Matches-cong p₁ q₁ ∣
                                        Matches-cong p₂ q₂
Matches-cong (p₁ ⊕ p₂)     (q₁ ⊕ q₂)  = Matches-cong p₁ q₁ ⊕
                                        Matches-cong p₂ q₂
Matches-cong (refl · p)    (action q) = action λ { .force →
                                          Matches-cong (force p)
                                                       (force q) }
Matches-cong (⟨ν refl ⟩ p) (⟨ν⟩ q)    = ⟨ν⟩ (Matches-cong p q)
Matches-cong (! p)         (! q)      = ! Matches-cong p q

-- A predicate that identifies a process as being finite. Note that
-- this is an inductive definition.

data Finite : Proc ∞ → Set ℓ where
  ∅      : Finite ∅
  _∣_    : ∀ {P Q} → Finite P → Finite Q → Finite (P ∣ Q)
  _⊕_    : ∀ {P Q} → Finite P → Finite Q → Finite (P ⊕ Q)
  action : ∀ {μ P} → Finite (force P) → Finite (μ · P)
  ⟨ν_⟩   : ∀ {a P} → Finite P → Finite (⟨ν a ⟩ P)
  !_     : ∀ {P} → Finite P → Finite (! P)

-- The transition relation takes finite processes to finite processes.

finite→finite : ∀ {P μ Q} → P [ μ ]⟶ Q → Finite P → Finite Q
finite→finite (par-left tr)       (f₁ ∣ f₂)  = finite→finite tr f₁ ∣ f₂
finite→finite (par-right tr)      (f₁ ∣ f₂)  = f₁ ∣ finite→finite tr f₂
finite→finite (par-τ tr₁ tr₂)     (f₁ ∣ f₂)  = finite→finite tr₁ f₁ ∣
                                               finite→finite tr₂ f₂
finite→finite (sum-left tr)       (f₁ ⊕ f₂)  = finite→finite tr f₁
finite→finite (sum-right tr)      (f₁ ⊕ f₂)  = finite→finite tr f₂
finite→finite action              (action f) = f
finite→finite (restriction a∉ tr) ⟨ν f ⟩     = ⟨ν finite→finite tr f ⟩
finite→finite (replication tr)    (! f)      = finite→finite tr (! f ∣ f)

-- Subprocess P Q means that P is a syntactic subprocess of Q.

data Subprocess (P : Proc ∞) : Proc ∞ → Set ℓ where
  refl        : ∀ {Q} → Equal ∞ P Q → Subprocess P Q
  par-left    : ∀ {Q₁ Q₂} → Subprocess P Q₁ → Subprocess P (Q₁ ∣ Q₂)
  par-right   : ∀ {Q₁ Q₂} → Subprocess P Q₂ → Subprocess P (Q₁ ∣ Q₂)
  sum-left    : ∀ {Q₁ Q₂} → Subprocess P Q₁ → Subprocess P (Q₁ ⊕ Q₂)
  sum-right   : ∀ {Q₁ Q₂} → Subprocess P Q₂ → Subprocess P (Q₁ ⊕ Q₂)
  action      : ∀ {μ Q} → Subprocess P (force Q) → Subprocess P (μ · Q)
  restriction : ∀ {a Q} → Subprocess P Q → Subprocess P (⟨ν a ⟩ Q)
  replication : ∀ {Q} → Subprocess P Q → Subprocess P (! Q)

-- A process is regular if it has a finite number of distinct
-- subprocesses.

Regular : Proc ∞ → Set ℓ
Regular P =
  ∃ λ n → ∃ λ (Qs : Fin n → Proc ∞) →
    ∀ {Q} → Subprocess Q P →
      ∃ λ (i : Fin n) → Equal ∞ Q (Qs i)

-- Lemma 6.2.15 from "Enhancements of the bisimulation proof method".
-- That text claims that the lemma is proved by induction on the
-- structure of the context. Perhaps that is possible, but the proof
-- below uses induction on the structure of the transition relation,
-- and in the replication case's recursive call the context is not
-- structurally smaller.

6-2-15 :
  ∀ {n Ps μ P}
  (C : Context ∞ n) → Weakly-guarded C →
  C [ Ps ] [ μ ]⟶ P →
  ∃ λ (C′ : Context ∞ n) →
    P ≡ C′ [ Ps ] × ∀ Qs → C [ Qs ] [ μ ]⟶ C′ [ Qs ]
6-2-15 ∅          ∅         ()
6-2-15 (C₁ ∣ C₂)  (w₁ ∣ w₂) (par-left  tr)       = Σ-map (_∣ C₂) (Σ-map (cong (_∣ _)) (par-left  ∘_)) (6-2-15 C₁ w₁ tr)
6-2-15 (C₁ ∣ C₂)  (w₁ ∣ w₂) (par-right tr)       = Σ-map (C₁ ∣_) (Σ-map (cong (_ ∣_)) (par-right ∘_)) (6-2-15 C₂ w₂ tr)
6-2-15 (C₁ ∣ C₂)  (w₁ ∣ w₂) (par-τ tr₁ tr₂)      = Σ-zip _∣_ (Σ-zip (cong₂ _)
                                                                    (λ trs₁ trs₂ Qs → par-τ (trs₁ Qs) (trs₂ Qs)))
                                                     (6-2-15 C₁ w₁ tr₁) (6-2-15 C₂ w₂ tr₂)
6-2-15 (C₁ ⊕ C₂)  (w₁ ⊕ w₂) (sum-left  tr)       = Σ-map id (Σ-map id (sum-left  ∘_)) (6-2-15 C₁ w₁ tr)
6-2-15 (C₁ ⊕ C₂)  (w₁ ⊕ w₂) (sum-right tr)       = Σ-map id (Σ-map id (sum-right ∘_)) (6-2-15 C₂ w₂ tr)
6-2-15 (μ · C)    action    action               = force C , refl , λ _ → action
6-2-15 (⟨ν a ⟩ C) (⟨ν⟩ w)   (restriction a∉μ tr) = Σ-map ⟨ν a ⟩ (Σ-map (cong _) (restriction a∉μ ∘_)) (6-2-15 C w tr)
6-2-15 (! C)      (! w)     (replication tr)     = Σ-map id (Σ-map id (replication ∘_)) (6-2-15 (! C ∣ C) (! w ∣ w) tr)

-- A variant of the previous lemma.

6-2-15-nd :
  Proc-extensionality →
  ∀ {n Ps μ P}
  (C : Context ∞ n) → Weakly-guarded C → Non-degenerate ∞ C →
  C [ Ps ] [ μ ]⟶ P →
  ∃ λ (C′ : Context ∞ n) →
    Non-degenerate ∞ C′ ×
    P ≡ C′ [ Ps ] × ∀ Qs → C [ Qs ] [ μ ]⟶ C′ [ Qs ]
6-2-15-nd ext ∅          ∅         ∅ ()
6-2-15-nd ext (C₁ ∣ C₂)  (w₁ ∣ w₂) (n₁ ∣ n₂)         (par-left  tr)       = Σ-map (_∣ C₂) (Σ-map (_∣ n₂) (Σ-map (cong (_∣ _)) (par-left  ∘_)))
                                                                              (6-2-15-nd ext C₁ w₁ n₁ tr)
6-2-15-nd ext (C₁ ∣ C₂)  (w₁ ∣ w₂) (n₁ ∣ n₂)         (par-right tr)       = Σ-map (C₁ ∣_) (Σ-map (n₁ ∣_) (Σ-map (cong (_ ∣_)) (par-right ∘_)))
                                                                              (6-2-15-nd ext C₂ w₂ n₂ tr)
6-2-15-nd ext (C₁ ∣ C₂)  (w₁ ∣ w₂) (n₁ ∣ n₂)         (par-τ tr₁ tr₂)      = Σ-zip _∣_ (Σ-zip _∣_ (Σ-zip (cong₂ _) (λ trs₁ trs₂ Qs →
                                                                                                                       par-τ (trs₁ Qs) (trs₂ Qs))))
                                                                              (6-2-15-nd ext C₁ w₁ n₁ tr₁) (6-2-15-nd ext C₂ w₂ n₂ tr₂)
6-2-15-nd ext (μ · C)    action    (action n)        action               = force C , force n , refl , λ _ → action
6-2-15-nd ext (⟨ν a ⟩ C) (⟨ν⟩ w)   (⟨ν⟩ n)           (restriction a∉μ tr) = Σ-map ⟨ν a ⟩ (Σ-map ⟨ν⟩ (Σ-map (cong _) (restriction a∉μ ∘_)))
                                                                              (6-2-15-nd ext C w n tr)
6-2-15-nd ext (! C)      (! w)     (! n)             (replication tr)     = Σ-map id (Σ-map id (Σ-map id (replication ∘_)))
                                                                              (6-2-15-nd ext (! C ∣ C) (! w ∣ w) (! n ∣ n) tr)
6-2-15-nd ext (C₁ ⊕ C₂)  (w₁ ⊕ w₂) (action n₁  ⊕ n₂) (sum-left  tr)       = Σ-map id (Σ-map id (Σ-map id (sum-left ∘_)))
                                                                              (6-2-15-nd ext (_ · _) action (action n₁) tr)
6-2-15-nd ext {Ps = Ps} {P = P}
              (C₁ ⊕ C₂)  (w₁ ⊕ w₂) (process P₁ ⊕ n₂) (sum-left  tr)       = context P , context-non-degenerate P , ext (context-[] P) , λ Qs →
                                                                              subst (_ [ _ ]⟶_) (ext $ context-[] P) $
                                                                              subst (λ P → P ⊕ _ [ _ ]⟶ _)
                                                                                    (context P₁ [ Ps ]  ≡⟨ sym $ ext $ context-[] P₁ ⟩
                                                                                     P₁                 ≡⟨ ext $ context-[] P₁ ⟩∎
                                                                                     context P₁ [ Qs ]  ∎) $
                                                                              sum-left tr
6-2-15-nd ext (C₁ ⊕ C₂)  (w₁ ⊕ w₂) (n₁ ⊕ action n₂)  (sum-right tr)       = Σ-map id (Σ-map id (Σ-map id (sum-right ∘_)))
                                                                              (6-2-15-nd ext (_ · _) action (action n₂) tr)
6-2-15-nd ext {Ps = Ps} {P = P}
              (C₁ ⊕ C₂)  (w₁ ⊕ w₂) (n₁ ⊕ process P₂) (sum-right tr)       = context P , context-non-degenerate P , ext (context-[] P) , λ Qs →
                                                                              subst (_ [ _ ]⟶_) (ext $ context-[] P) $
                                                                              subst (λ P → _ ⊕ P [ _ ]⟶ _)
                                                                                    (context P₂ [ Ps ]  ≡⟨ sym $ ext $ context-[] P₂ ⟩
                                                                                     P₂                 ≡⟨ ext $ context-[] P₂ ⟩∎
                                                                                     context P₂ [ Qs ]  ∎) $
                                                                              sum-right tr
