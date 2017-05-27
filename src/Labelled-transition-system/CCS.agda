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
-- CCS, roughly as defined in "Enhancements of the bisimulation
-- proof method" by Pous and Sangiorgi

Name-with-kind : Set
Name-with-kind = Name × Bool

co : Name-with-kind → Name-with-kind
co (a , kind) = a , not kind

data Action : Set where
  τ    : Action
  name : Name-with-kind → Action

infix  12 _·
infixr 12 _·_
infix  10 !_
infix   8 _⊕_
infix   6 _∣_
infix   5 _[_]
infix   4 _[_]⟶_ _∉_

data Proc : Set where
  ∅       : Proc
  _∣_ _⊕_ : Proc → Proc → Proc
  _·_     : Action → Proc → Proc
  ν       : Name → Proc → Proc
  !_      : Proc → Proc

_· : Name-with-kind → Proc
a · = name a · ∅

_∉_ : Name → Action → Set
a ∉ τ            = ⊤
a ∉ name (b , _) = a ≢ b

data _[_]⟶_ : Proc → Action → Proc → Set where
  par-left     : ∀ {P Q P′ μ} → P [ μ ]⟶ P′ → P ∣ Q [ μ ]⟶ P′ ∣ Q
  par-right    : ∀ {P Q Q′ μ} → Q [ μ ]⟶ Q′ → P ∣ Q [ μ ]⟶ P  ∣ Q′
  par-τ′       : ∀ {P P′ Q Q′ a b} →
                 b ≡ co a → P [ name a ]⟶ P′ → Q [ name b ]⟶ Q′ →
                 P ∣ Q [ τ ]⟶ P′ ∣ Q′
  choice-left  : ∀ {P Q P′ μ} → P [ μ ]⟶ P′ → P ⊕ Q [ μ ]⟶ P′
  choice-right : ∀ {P Q Q′ μ} → Q [ μ ]⟶ Q′ → P ⊕ Q [ μ ]⟶ Q′
  action       : ∀ {P μ} → μ · P [ μ ]⟶ P
  restriction  : ∀ {P P′ a μ} →
                 a ∉ μ → P [ μ ]⟶ P′ → ν a P [ μ ]⟶ ν a P′
  replication  : ∀ {P P′ μ} → ! P ∣ P [ μ ]⟶ P′ → ! P [ μ ]⟶ P′

pattern par-τ {P} {P′} {Q} {Q′} {a} tr₁ tr₂ =
  par-τ′ {P} {P′} {Q} {Q′} {a} refl tr₁ tr₂

CCS : LTS
CCS = record
  { Proc    = Proc
  ; Label   = Action
  ; Silent  = _≡ τ
  ; silent? = λ { τ        → yes refl
                ; (name _) → no λ ()
                }
  ; _[_]⟶_  = _[_]⟶_
  }

open LTS CCS public hiding (Proc; _[_]⟶_)

-- Polyadic contexts.

data Context (n : ℕ) : Set where
  hole    : (x : Fin n) → Context n
  ∅       : Context n
  _∣_ _⊕_ : Context n → Context n → Context n
  _·_     : (μ : Action) → Context n → Context n
  ν       : (a : Name) → Context n → Context n
  !_      : Context n → Context n

-- Hole filling.

_[_] : ∀ {n} → Context n → (Fin n → Proc) → Proc
hole x  [ ps ] = ps x
∅       [ ps ] = ∅
C₁ ∣ C₂ [ ps ] = (C₁ [ ps ]) ∣ (C₂ [ ps ])
C₁ ⊕ C₂ [ ps ] = (C₁ [ ps ]) ⊕ (C₂ [ ps ])
μ · C   [ ps ] = μ · (C [ ps ])
ν a C   [ ps ] = ν a (C [ ps ])
! C     [ ps ] = ! (C [ ps ])

-- Weakly guarded contexts.

data Weakly-guarded {n : ℕ} : Context n → Set where
  ∅      : Weakly-guarded ∅
  _∣_    : ∀ {C₁ C₂} →
           Weakly-guarded C₁ → Weakly-guarded C₂ →
           Weakly-guarded (C₁ ∣ C₂)
  _⊕_    : ∀ {C₁ C₂} →
           Weakly-guarded C₁ → Weakly-guarded C₂ →
           Weakly-guarded (C₁ ⊕ C₂)
  action : ∀ {μ C} → Weakly-guarded (μ · C)
  ν      : ∀ {a C} → Weakly-guarded C → Weakly-guarded (ν a C)
  !_     : ∀ {C} → Weakly-guarded C → Weakly-guarded (! C)

-- Turns processes into contexts without holes.

context : ∀ {n} → Proc → Context n
context ∅         = ∅
context (P₁ ∣ P₂) = context P₁ ∣ context P₂
context (P₁ ⊕ P₂) = context P₁ ⊕ context P₂
context (μ · P)   = μ · context P
context (ν a P)   = ν a (context P)
context (! P)     = ! context P

-- Non-degenerate contexts.

mutual

  data Non-degenerate {n : ℕ} : Context n → Set where
    hole   : ∀ {x} → Non-degenerate (hole x)
    ∅      : Non-degenerate ∅
    _∣_    : ∀ {C₁ C₂} →
             Non-degenerate C₁ → Non-degenerate C₂ →
             Non-degenerate (C₁ ∣ C₂)
    _⊕_    : ∀ {C₁ C₂} →
             Non-degenerate-summand C₁ → Non-degenerate-summand C₂ →
             Non-degenerate (C₁ ⊕ C₂)
    action : ∀ {μ C} → Non-degenerate C → Non-degenerate (μ · C)
    ν      : ∀ {a C} → Non-degenerate C → Non-degenerate (ν a C)
    !_     : ∀ {C} → Non-degenerate C → Non-degenerate (! C)

  data Non-degenerate-summand {n : ℕ} : Context n → Set where
    process : ∀ P → Non-degenerate-summand (context P)
    action  : ∀ {μ C} →
              Non-degenerate C → Non-degenerate-summand (μ · C)

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

-- The process μ · P can only make μ-transitions.

·-only : ∀ {μ₁ μ₂ P Q} → μ₁ · P [ μ₂ ]⟶ Q → μ₁ ≡ μ₂
·-only action = refl

-- The process μ · P can only transition to P.

·-only⟶ : ∀ {μ₁ μ₂ P Q} → μ₁ · P [ μ₂ ]⟶ Q → Q ≡ P
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
⊕-only only₁ only₂ (choice-left tr)  = only₁ tr
⊕-only only₁ only₂ (choice-right tr) = only₂ tr

-- A simple lemma.

·⊕·-co :
  ∀ {a b c P Q R S} →
  name a · P ⊕ name b · Q [ name c ]⟶      R →
  name a · P ⊕ name b · Q [ name (co c) ]⟶ S →
  b ≡ co a × (R ≡ P × S ≡ Q ⊎ R ≡ Q × S ≡ P)
·⊕·-co (choice-left  action)
       (choice-left  tr)     = ⊥-elim (names-are-not-inverted tr)
·⊕·-co (choice-left  action)
       (choice-right action) = refl , inj₁ (refl , refl)
·⊕·-co (choice-right action)
       (choice-left  action) =   sym (co-involutive _)
                               , inj₂ (refl , refl)
·⊕·-co (choice-right action)
       (choice-right tr)     = ⊥-elim (names-are-not-inverted tr)

-- Lemma 6.2.15 from "Enhancements of the bisimulation proof
-- method". That text claims that the lemma is proved by induction
-- on the structure of the context. Perhaps that is possible, but
-- the proof below uses induction on the structure of the transition
-- relation, and in the final case's recursive call the context is
-- not structurally smaller.

6-2-15 :
  ∀ {n Ps μ P}
  (C : Context n) → Weakly-guarded C →
  C [ Ps ] [ μ ]⟶ P →
  ∃ λ (C′ : Context n) →
    P ≡ C′ [ Ps ] × ∀ Qs → C [ Qs ] [ μ ]⟶ C′ [ Qs ]
6-2-15 ∅         ∅         ()
6-2-15 (C₁ ∣ C₂) (w₁ ∣ w₂) (par-left  tr)       = Σ-map (_∣ C₂) (Σ-map (cong (_∣ _)) (par-left  ∘_)) (6-2-15 C₁ w₁ tr)
6-2-15 (C₁ ∣ C₂) (w₁ ∣ w₂) (par-right tr)       = Σ-map (C₁ ∣_) (Σ-map (cong (_ ∣_)) (par-right ∘_)) (6-2-15 C₂ w₂ tr)
6-2-15 (C₁ ∣ C₂) (w₁ ∣ w₂) (par-τ tr₁ tr₂)      = Σ-zip _∣_ (Σ-zip (cong₂ _)
                                                                   (λ trs₁ trs₂ Qs → par-τ (trs₁ Qs) (trs₂ Qs)))
                                                    (6-2-15 C₁ w₁ tr₁) (6-2-15 C₂ w₂ tr₂)
6-2-15 (C₁ ⊕ C₂) (w₁ ⊕ w₂) (choice-left  tr)    = Σ-map id (Σ-map id (choice-left  ∘_)) (6-2-15 C₁ w₁ tr)
6-2-15 (C₁ ⊕ C₂) (w₁ ⊕ w₂) (choice-right tr)    = Σ-map id (Σ-map id (choice-right ∘_)) (6-2-15 C₂ w₂ tr)
6-2-15 (μ · C)   action    action               = C , refl , λ _ → action
6-2-15 (ν a C)   (ν w)     (restriction a∉μ tr) = Σ-map (ν a) (Σ-map (cong _) (restriction a∉μ ∘_)) (6-2-15 C w tr)
6-2-15 (! C)     (! w)     (replication tr)     = Σ-map id (Σ-map id (replication ∘_)) (6-2-15 (! C ∣ C) (! w ∣ w) tr)

-- Weakening of contexts.

weaken : ∀ {n} → Context n → Context (suc n)
weaken (hole x)  = hole (fsuc x)
weaken ∅         = ∅
weaken (C₁ ∣ C₂) = weaken C₁ ∣ weaken C₂
weaken (C₁ ⊕ C₂) = weaken C₁ ⊕ weaken C₂
weaken (μ · C)   = μ · weaken C
weaken (ν a C)   = ν a (weaken C)
weaken (! C)     = ! weaken C

-- A lemma relating weakening and hole filling.

weaken-[] :
  ∀ {n ps} (C : Context n) →
  weaken C [ ps ] ≡ C [ ps ∘ fsuc ]
weaken-[] (hole x)  = refl
weaken-[] ∅         = refl
weaken-[] (C₁ ∣ C₂) = cong₂ _∣_ (weaken-[] C₁) (weaken-[] C₂)
weaken-[] (C₁ ⊕ C₂) = cong₂ _⊕_ (weaken-[] C₁) (weaken-[] C₂)
weaken-[] (μ · C)   = cong (μ ·_) (weaken-[] C)
weaken-[] (ν a C)   = cong (ν a) (weaken-[] C)
weaken-[] (! C)     = cong !_ (weaken-[] C)

-- The result of filling the holes in the context "context P" is P.

context-[] : ∀ {n} {Ps : Fin n → Proc} P → context P [ Ps ] ≡ P
context-[] ∅         = refl
context-[] (P₁ ∣ P₂) = cong₂ _∣_ (context-[] P₁) (context-[] P₂)
context-[] (P₁ ⊕ P₂) = cong₂ _⊕_ (context-[] P₁) (context-[] P₂)
context-[] (μ · P)   = cong (μ ·_) (context-[] P)
context-[] (ν a P)   = cong (ν a) (context-[] P)
context-[] (! P)     = cong !_ (context-[] P)

-- A relation expressing that a certain process matches a certain
-- context.

data Matches {n} : Proc → Context n → Set where
  hole   : ∀ {P} (x : Fin n) → Matches P (hole x)
  ∅      : Matches ∅ ∅
  _∣_    : ∀ {P₁ P₂ C₁ C₂} →
           Matches P₁ C₁ → Matches P₂ C₂ → Matches (P₁ ∣ P₂) (C₁ ∣ C₂)
  _⊕_    : ∀ {P₁ P₂ C₁ C₂} →
           Matches P₁ C₁ → Matches P₂ C₂ → Matches (P₁ ⊕ P₂) (C₁ ⊕ C₂)
  action : ∀ {μ P C} → Matches P C → Matches (μ · P) (μ · C)
  ν      : ∀ {a P C} → Matches P C → Matches (ν a P) (ν a C)
  !_     : ∀ {P C} → Matches P C → Matches (! P) (! C)

-- The process obtained by filling a context's holes matches the
-- context.

Matches-[] : ∀ {n Ps} (C : Context n) → Matches (C [ Ps ]) C
Matches-[] (hole x)  = hole x
Matches-[] ∅         = ∅
Matches-[] (C₁ ∣ C₂) = Matches-[] C₁ ∣ Matches-[] C₂
Matches-[] (C₁ ⊕ C₂) = Matches-[] C₁ ⊕ Matches-[] C₂
Matches-[] (μ · C)   = action (Matches-[] C)
Matches-[] (ν a C)   = ν (Matches-[] C)
Matches-[] (! C)     = ! Matches-[] C
