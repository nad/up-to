------------------------------------------------------------------------
-- CCS
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Labelled-transition-system.CCS (Name : Set) where

open import Equality.Propositional
open import Prelude

open import Bool equality-with-J
open import Function-universe equality-with-J hiding (id; _∘_)

open import Labelled-transition-system

------------------------------------------------------------------------
-- CCS, roughly as defined in "Enhancements of the bisimulation proof
-- method" by Pous and Sangiorgi, with support for corecursive
-- processes (instead of the named process constants presented in
-- "Coinduction All the Way Up" by Pous)

Name-with-kind : Set
Name-with-kind = Name × Bool

co : Name-with-kind → Name-with-kind
co (a , kind) = a , not kind

data Action : Set where
  τ    : Action
  name : Name-with-kind → Action

infix  12 _·
infixr 12 _·′_ _·_
infix  10 !_
infix   8 _⊕_
infix   6 _∣_
infix   5 _[_] _[_]′
infix   4 _[_]⟶_ _∉_

mutual

  data Proc (i : Size) : Set where
    ∅       : Proc i
    _∣_ _⊕_ : Proc i → Proc i → Proc i
    _·′_    : Action → Proc′ i → Proc i
    ν       : Name → Proc i → Proc i
    !_      : Proc i → Proc i

  record Proc′ (i : Size) : Set where
    coinductive
    field
      force : {j : Size< i} → Proc j

open Proc′ public

_·_ : ∀ {i} → Action → Proc i → Proc i
μ · P = μ ·′ λ { .force → P }

_· : Name-with-kind → Proc ∞
a · = name a · ∅

_∉_ : Name → Action → Set
a ∉ τ            = ⊤
a ∉ name (b , _) = a ≢ b

data _[_]⟶_ : Proc ∞ → Action → Proc ∞ → Set where
  par-left     : ∀ {P Q P′ μ} → P [ μ ]⟶ P′ → P ∣ Q [ μ ]⟶ P′ ∣ Q
  par-right    : ∀ {P Q Q′ μ} → Q [ μ ]⟶ Q′ → P ∣ Q [ μ ]⟶ P  ∣ Q′
  par-τ′       : ∀ {P P′ Q Q′ a b} →
                 b ≡ co a → P [ name a ]⟶ P′ → Q [ name b ]⟶ Q′ →
                 P ∣ Q [ τ ]⟶ P′ ∣ Q′
  choice-left  : ∀ {P Q P′ μ} → P [ μ ]⟶ P′ → P ⊕ Q [ μ ]⟶ P′
  choice-right : ∀ {P Q Q′ μ} → Q [ μ ]⟶ Q′ → P ⊕ Q [ μ ]⟶ Q′
  action       : ∀ {P μ} → μ ·′ P [ μ ]⟶ force P
  restriction  : ∀ {P P′ a μ} →
                 a ∉ μ → P [ μ ]⟶ P′ → ν a P [ μ ]⟶ ν a P′
  replication  : ∀ {P P′ μ} → ! P ∣ P [ μ ]⟶ P′ → ! P [ μ ]⟶ P′

pattern par-τ {P} {P′} {Q} {Q′} {a} tr₁ tr₂ =
  par-τ′ {P} {P′} {Q} {Q′} {a} refl tr₁ tr₂

CCS : LTS
CCS = record
  { Proc    = Proc ∞
  ; Label   = Action
  ; Silent  = _≡ τ
  ; silent? = λ { τ        → yes refl
                ; (name _) → no λ ()
                }
  ; _[_]⟶_  = _[_]⟶_
  }

open LTS CCS public hiding (Proc; _[_]⟶_)

mutual

  -- Polyadic contexts.

  data Context (i : Size) (n : ℕ) : Set where
    hole    : (x : Fin n) → Context i n
    ∅       : Context i n
    _∣_ _⊕_ : Context i n → Context i n → Context i n
    _·′_    : (μ : Action) → Context′ i n → Context i n
    ν       : (a : Name) → Context i n → Context i n
    !_      : Context i n → Context i n

  record Context′ (i : Size) (n : ℕ) : Set where
    coinductive
    field
      force : {j : Size< i} → Context j n

open Context′ public

mutual

  -- Hole filling.

  _[_] : ∀ {i n} → Context i n → (Fin n → Proc ∞) → Proc i
  hole x  [ Ps ] = Ps x
  ∅       [ Ps ] = ∅
  C₁ ∣ C₂ [ Ps ] = (C₁ [ Ps ]) ∣ (C₂ [ Ps ])
  C₁ ⊕ C₂ [ Ps ] = (C₁ [ Ps ]) ⊕ (C₂ [ Ps ])
  μ ·′ C  [ Ps ] = μ ·′ (C [ Ps ]′)
  ν a C   [ Ps ] = ν a (C [ Ps ])
  ! C     [ Ps ] = ! (C [ Ps ])

  _[_]′ : ∀ {i n} → Context′ i n → (Fin n → Proc ∞) → Proc′ i
  force (C [ Ps ]′) = force C [ Ps ]

data Weakly-guarded {n : ℕ} : Context ∞ n → Set where
  ∅      : Weakly-guarded ∅
  _∣_    : ∀ {C₁ C₂} →
           Weakly-guarded C₁ → Weakly-guarded C₂ →
           Weakly-guarded (C₁ ∣ C₂)
  _⊕_    : ∀ {C₁ C₂} →
           Weakly-guarded C₁ → Weakly-guarded C₂ →
           Weakly-guarded (C₁ ⊕ C₂)
  action : ∀ {μ C} → Weakly-guarded (μ ·′ C)
  ν      : ∀ {a C} → Weakly-guarded C → Weakly-guarded (ν a C)
  !_     : ∀ {C} → Weakly-guarded C → Weakly-guarded (! C)

-- Turns processes into contexts without holes.

context : ∀ {i n} → Proc i → Context i n
context ∅         = ∅
context (P₁ ∣ P₂) = context P₁ ∣ context P₂
context (P₁ ⊕ P₂) = context P₁ ⊕ context P₂
context (μ ·′ P)  = μ ·′ λ { .force → context (force P) }
context (ν a P)   = ν a (context P)
context (! P)     = ! context P

-- Non-degenerate contexts.

mutual

  data Non-degenerate (i : Size) {n : ℕ} : Context ∞ n → Set where
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
             Non-degenerate′ i (force C) → Non-degenerate i (μ ·′ C)
    ν      : ∀ {a C} → Non-degenerate i C → Non-degenerate i (ν a C)
    !_     : ∀ {C} → Non-degenerate i C → Non-degenerate i (! C)

  data Non-degenerate-summand (i : Size) {n : ℕ} :
                              Context ∞ n → Set where
    process : ∀ P → Non-degenerate-summand i (context P)
    action  : ∀ {μ C} →
              Non-degenerate′ i (force C) →
              Non-degenerate-summand i (μ ·′ C)

  record Non-degenerate′ (i : Size) {n} (C : Context ∞ n) : Set where
    coinductive
    field
      force : {j : Size< i} → Non-degenerate j C

open Non-degenerate′ public

-- "Very strong" bisimilarity for processes.

mutual

  data Equal (i : Size) : Proc ∞ → Proc ∞ → Set where
    ∅    : Equal i ∅ ∅
    _∣_  : ∀ {P₁ P₂ Q₁ Q₂} →
           Equal i P₁ P₂ → Equal i Q₁ Q₂ → Equal i (P₁ ∣ Q₁) (P₂ ∣ Q₂)
    _⊕_  : ∀ {P₁ P₂ Q₁ Q₂} →
           Equal i P₁ P₂ → Equal i Q₁ Q₂ → Equal i (P₁ ⊕ Q₁) (P₂ ⊕ Q₂)
    _·′_ : ∀ {μ₁ μ₂ P₁ P₂} →
           μ₁ ≡ μ₂ → Equal′ i (force P₁) (force P₂) →
           Equal i (μ₁ ·′ P₁) (μ₂ ·′ P₂)
    ν    : ∀ {a₁ a₂ P₁ P₂} →
           a₁ ≡ a₂ → Equal i P₁ P₂ → Equal i (ν a₁ P₁) (ν a₂ P₂)
    !_   : ∀ {P₁ P₂} → Equal i P₁ P₂ → Equal i (! P₁) (! P₂)

  record Equal′ (i : Size) (P₁ P₂ : Proc ∞) : Set where
    coinductive
    field
      force : {j : Size< i} → Equal j P₁ P₂

open Equal′ public

-- Extensionality for very strong bisimilarity.

Proc-extensionality : Set
Proc-extensionality = ∀ {P Q} → Equal ∞ P Q → P ≡ Q

------------------------------------------------------------------------
-- A bunch of simple lemmas

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

-- The process μ ·′ P can only make μ-transitions.

·′-only : ∀ {μ₁ μ₂ P Q} → μ₁ ·′ P [ μ₂ ]⟶ Q → μ₁ ≡ μ₂
·′-only action = refl

-- The process μ ·′ P can only transition to force P.

·′-only⟶ : ∀ {μ₁ μ₂ P Q} → μ₁ ·′ P [ μ₂ ]⟶ Q → Q ≡ force P
·′-only⟶ action = refl

-- A simple corollary.

names-are-not-inverted :
  ∀ {a P Q} → ¬ (name a ·′ P [ name (co a) ]⟶ Q)
names-are-not-inverted {a} {P} {Q} =
  name a ·′ P [ name (co a) ]⟶ Q  ↝⟨ ·′-only ⟩
  name a ≡ name (co a)            ↝⟨ id≢co ∘ cancel-name ⟩□
  ⊥                               □

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
⊕-only only₁ only₂ (choice-left tr)  = only₁ tr
⊕-only only₁ only₂ (choice-right tr) = only₂ tr

-- If P can only make μ-transitions, then ν a P can only make
-- μ-transitions.

ν-only : ∀ {μ₀ a P} →
         (∀ {P′ μ} → P [ μ ]⟶ P′ → μ₀ ≡ μ) →
         ∀ {P′ μ} → ν a P [ μ ]⟶ P′ → μ₀ ≡ μ
ν-only only (restriction _ tr) = only tr

-- A simple lemma.

·′⊕·′-co :
  ∀ {a b c P Q R S} →
  name a ·′ P ⊕ name b ·′ Q [ name c ]⟶      R →
  name a ·′ P ⊕ name b ·′ Q [ name (co c) ]⟶ S →
  b ≡ co a × (R ≡ force P × S ≡ force Q ⊎ R ≡ force Q × S ≡ force P)
·′⊕·′-co (choice-left  action)
         (choice-left  tr)     = ⊥-elim (names-are-not-inverted tr)
·′⊕·′-co (choice-left  action)
         (choice-right action) = refl , inj₁ (refl , refl)
·′⊕·′-co (choice-right action)
         (choice-left  action) =   sym (co-involutive _)
                                 , inj₂ (refl , refl)
·′⊕·′-co (choice-right action)
         (choice-right tr)     = ⊥-elim (names-are-not-inverted tr)

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
6-2-15 ∅         ∅         ()
6-2-15 (C₁ ∣ C₂) (w₁ ∣ w₂) (par-left  tr)       = Σ-map (_∣ C₂) (Σ-map (cong (_∣ _)) (par-left  ∘_)) (6-2-15 C₁ w₁ tr)
6-2-15 (C₁ ∣ C₂) (w₁ ∣ w₂) (par-right tr)       = Σ-map (C₁ ∣_) (Σ-map (cong (_ ∣_)) (par-right ∘_)) (6-2-15 C₂ w₂ tr)
6-2-15 (C₁ ∣ C₂) (w₁ ∣ w₂) (par-τ tr₁ tr₂)      = Σ-zip _∣_ (Σ-zip (cong₂ _)
                                                                   (λ trs₁ trs₂ Qs → par-τ (trs₁ Qs) (trs₂ Qs)))
                                                    (6-2-15 C₁ w₁ tr₁) (6-2-15 C₂ w₂ tr₂)
6-2-15 (C₁ ⊕ C₂) (w₁ ⊕ w₂) (choice-left  tr)    = Σ-map id (Σ-map id (choice-left  ∘_)) (6-2-15 C₁ w₁ tr)
6-2-15 (C₁ ⊕ C₂) (w₁ ⊕ w₂) (choice-right tr)    = Σ-map id (Σ-map id (choice-right ∘_)) (6-2-15 C₂ w₂ tr)
6-2-15 (μ ·′ C)  action    action               = force C , refl , λ _ → action
6-2-15 (ν a C)   (ν w)     (restriction a∉μ tr) = Σ-map (ν a) (Σ-map (cong _) (restriction a∉μ ∘_)) (6-2-15 C w tr)
6-2-15 (! C)     (! w)     (replication tr)     = Σ-map id (Σ-map id (replication ∘_)) (6-2-15 (! C ∣ C) (! w ∣ w) tr)

-- Very strong bisimilarity is reflexive.

Proc-refl : ∀ {i} P → Equal i P P
Proc-refl ∅         = ∅
Proc-refl (P₁ ∣ P₂) = Proc-refl P₁ ∣ Proc-refl P₂
Proc-refl (P₁ ⊕ P₂) = Proc-refl P₁ ⊕ Proc-refl P₂
Proc-refl (μ ·′ P)  = refl ·′ λ { .force → Proc-refl (force P) }
Proc-refl (ν a P)   = ν refl (Proc-refl P)
Proc-refl (! P)     = ! Proc-refl P

-- Weakening of contexts.

weaken : ∀ {i n} → Context i n → Context i (suc n)
weaken (hole x)  = hole (fsuc x)
weaken ∅         = ∅
weaken (C₁ ∣ C₂) = weaken C₁ ∣ weaken C₂
weaken (C₁ ⊕ C₂) = weaken C₁ ⊕ weaken C₂
weaken (μ ·′ C)  = μ ·′ λ { .force → weaken (force C) }
weaken (ν a C)   = ν a (weaken C)
weaken (! C)     = ! weaken C

-- A lemma relating weakening and hole filling.

weaken-[] :
  ∀ {i n ps} (C : Context ∞ n) →
  Equal i (weaken C [ ps ]) (C [ ps ∘ fsuc ])
weaken-[] (hole x)  = Proc-refl _
weaken-[] ∅         = ∅
weaken-[] (C₁ ∣ C₂) = weaken-[] C₁ ∣ weaken-[] C₂
weaken-[] (C₁ ⊕ C₂) = weaken-[] C₁ ⊕ weaken-[] C₂
weaken-[] (μ ·′ C)  = refl ·′ λ { .force → weaken-[] (force C) }
weaken-[] (ν a C)   = ν refl (weaken-[] C)
weaken-[] (! C)     = ! weaken-[] C

-- The result of filling the holes in the context "context P" is P.

context-[] : ∀ {i n} {Ps : Fin n → Proc ∞} P →
             Equal i P (context P [ Ps ])
context-[] ∅         = ∅
context-[] (P₁ ∣ P₂) = context-[] P₁ ∣ context-[] P₂
context-[] (P₁ ⊕ P₂) = context-[] P₁ ⊕ context-[] P₂
context-[] (μ ·′ P)  = refl ·′ λ { .force → context-[] (force P) }
context-[] (ν a P)   = ν refl (context-[] P)
context-[] (! P)     = ! (context-[] P)

mutual

  -- A relation expressing that a certain process matches a certain
  -- context.

  data Matches (i : Size) {n} : Proc ∞ → Context ∞ n → Set where
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
             Matches i (μ ·′ P) (μ ·′ C)
    ν      : ∀ {a P C} → Matches i P C → Matches i (ν a P) (ν a C)
    !_     : ∀ {P C} → Matches i P C → Matches i (! P) (! C)

  record Matches′
           (i : Size) {n} (P : Proc ∞) (C : Context ∞ n) : Set where
    coinductive
    field
      force : {j : Size< i} → Matches j P C

open Matches′ public

-- The process obtained by filling a context's holes matches the
-- context.

Matches-[] : ∀ {i n Ps} (C : Context ∞ n) → Matches i (C [ Ps ]) C
Matches-[] (hole x)  = hole x
Matches-[] ∅         = ∅
Matches-[] (C₁ ∣ C₂) = Matches-[] C₁ ∣ Matches-[] C₂
Matches-[] (C₁ ⊕ C₂) = Matches-[] C₁ ⊕ Matches-[] C₂
Matches-[] (μ ·′ C)  = action λ { .force → Matches-[] (force C) }
Matches-[] (ν a C)   = ν (Matches-[] C)
Matches-[] (! C)     = ! Matches-[] C
