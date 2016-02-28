------------------------------------------------------------------------
-- Labelled transition systems
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Labelled-transition-system where

open import Equality.Propositional
open import Prelude

open import Bijection equality-with-J using (_↔_)
open import Bool equality-with-J
open import Equivalence equality-with-J using (↔⇒≃)
open import Function-universe equality-with-J hiding (id; _∘_)
open import Univalence-axiom equality-with-J

-- Labelled transition systems were perhaps first defined by Robert M.
-- Keller (http://dx.doi.org/10.1145/360248.360251). The definition
-- below is a variant with two fields "Silent" and "silent?", added by
-- me.
--
-- I don't know who first came up with the concept of a weak
-- transition. The definitions of _⇒_, _[_]⇒_ and _[_]⇒̂_ below are
-- based on definitions in "Enhancements of the bisimulation proof
-- method" by Pous and Sangiorgi.

record LTS : Set₁ where
  infix 4 _[_]⟶_ _⇒_ _[_]⇒_
  field
    -- Processes.
    Proc : Set

    -- Labels.
    Label : Set

    -- Is the label silent?
    Silent : Label → Set

    -- Silence can be decided.
    silent? : ∀ μ → Dec (Silent μ)

    -- Transitions.
    _[_]⟶_ : Proc → Label → Proc → Set

  -- Sequences of zero or more silent transitions.

  data _⇒_ : Proc → Proc → Set where
    done : ∀ {p} → p ⇒ p
    step : ∀ {p q r μ} → Silent μ → p [ μ ]⟶ q → q ⇒ r → p ⇒ r

  -- Weak transitions (one kind).

  data _[_]⇒_ (p : Proc) (μ : Label) (q : Proc) : Set where
    steps : ∀ {p′ q′} → p ⇒ p′ → p′ [ μ ]⟶ q′ → q′ ⇒ q → p [ μ ]⇒ q

  -- Weak transitions (another kind).

  data _[_]⇒̂_ (p : Proc) (μ : Label) (q : Proc) : Set where
    silent     : Silent μ → p ⇒ q → p [ μ ]⇒̂ q
    non-silent : ¬ Silent μ → p [ μ ]⇒ q → p [ μ ]⇒̂ q

  -- Regular transitions can be turned into weak ones.

  ⟶⇒⇒ : ∀ {p μ q} → p [ μ ]⟶ q → p [ μ ]⇒ q
  ⟶⇒⇒ tr = steps done tr done

  ⟶⇒⇒̂ : ∀ {p μ q} → p [ μ ]⟶ q → p [ μ ]⇒̂ q
  ⟶⇒⇒̂ {μ = μ} tr with silent? μ
  ... | yes s = silent s (step s tr done)
  ... | no ¬s = non-silent ¬s (⟶⇒⇒ tr)

  -- Another conversion function.

  ⇒̂→⇒ : ∀ {p q μ} → Silent μ → p [ μ ]⇒̂ q → p ⇒ q
  ⇒̂→⇒ s (silent _ p⇒q)    = p⇒q
  ⇒̂→⇒ s (non-silent ¬s _) = ⊥-elim (¬s s)

  -- Several transitivity-like properties.

  ⇒-transitive : ∀ {p q r} → p ⇒ q → q ⇒ r → p ⇒ r
  ⇒-transitive done             p⇒q = p⇒q
  ⇒-transitive (step s p⟶q q⇒r) r⇒s = step s p⟶q (⇒-transitive q⇒r r⇒s)

  ⇒⇒̂-transitive : ∀ {p q r μ} → p ⇒ q → q [ μ ]⇒̂ r → p [ μ ]⇒̂ r
  ⇒⇒̂-transitive p⇒q (silent s q⇒r) = silent s (⇒-transitive p⇒q q⇒r)
  ⇒⇒̂-transitive p⇒q (non-silent ¬s (steps q⇒r r⟶s s⇒t)) =
    non-silent ¬s (steps (⇒-transitive p⇒q q⇒r) r⟶s s⇒t)

  ⇒̂⇒-transitive : ∀ {p q r μ} → p [ μ ]⇒̂ q → q ⇒ r → p [ μ ]⇒̂ r
  ⇒̂⇒-transitive (silent s p⇒q) q⇒r = silent s (⇒-transitive p⇒q q⇒r)
  ⇒̂⇒-transitive (non-silent ¬s (steps p⇒q q⟶r r⇒s)) s⇒t =
    non-silent ¬s (steps p⇒q q⟶r (⇒-transitive r⇒s s⇒t))

  -- A lemma that can be used to show that some relation is a weak
  -- bisimulation (of a certain kind).

  is-weak :
    {_%_ _%′_ : Proc → Proc → Set}
    {_[_]%_ : Proc → Label → Proc → Set} →
    (∀ {p q} → p % q → ∀ {p′ μ} →
     p [ μ ]⟶ p′ → ∃ λ q′ → q [ μ ]% q′ × p′ %′ q′) →
    (∀ {p q} → p %′ q → p % q) →
    (∀ {p p′ μ} → Silent μ → p [ μ ]% p′ → p ⇒ p′) →
    (∀ {p p′ μ} → p [ μ ]% p′ → p [ μ ]⇒̂ p′) →
    ∀ {p p′ q μ} →
    p % q → p [ μ ]⇒̂ p′ →
    ∃ λ q′ → q [ μ ]⇒̂ q′ × (p′ % q′)
  is-weak {_%_} left-to-right %′⇒% %⇒⇒ %⇒⇒̂ = lr⇒̂
    where
    lr⇒ : ∀ {q q′ r} →
          q % r → q ⇒ q′ →
          ∃ λ r′ → r ⇒ r′ × (q′ % r′)
    lr⇒ q%r done                = _ , done , q%r
    lr⇒ q%r (step s q⟶q′ q′⇒q″) =
      let r′ , r%r′  , q′%′r′ = left-to-right q%r q⟶q′
          r″ , r′⇒r″ , q″%r″  = lr⇒ (%′⇒% q′%′r′) q′⇒q″
      in r″ , ⇒-transitive (%⇒⇒ s r%r′) r′⇒r″ , q″%r″

    lr⇒̂ : ∀ {p p′ q μ} →
          p % q → p [ μ ]⇒̂ p′ →
          ∃ λ q′ → q [ μ ]⇒̂ q′ × (p′ % q′)
    lr⇒̂ q%r (silent s q⇒q′) =
      let r′ , r⇒r′ , q′%r′ = lr⇒ q%r q⇒q′
      in r′ , silent s r⇒r′ , q′%r′
    lr⇒̂ q%r (non-silent ¬s (steps q⇒q′ q′⟶q″ q″⇒q‴)) =
      let r′ , r⇒r′  , r′%q′  = lr⇒ q%r q⇒q′
          r″ , r′%r″ , r″%′q″ = left-to-right r′%q′ q′⟶q″
          r‴ , r″⇒r‴ , r‴≈q‴  = lr⇒ (%′⇒% r″%′q″) q″⇒q‴
      in r‴ , ⇒⇒̂-transitive r⇒r′ (⇒̂⇒-transitive (%⇒⇒̂ r′%r″) r″⇒r‴)
            , r‴≈q‴

  -- If no action is silent, then _[_]⇒_ is pointwise isomorphic to
  -- _[_]⟶_.

  ⟶↔⇒ : (∀ μ → ¬ Silent μ) →
        ∀ {p μ q} → p [ μ ]⟶ q ↔ p [ μ ]⇒ q
  ⟶↔⇒ ¬silent = record
    { surjection = record
      { logical-equivalence = record
        { to   = ⟶⇒⇒
        ; from = λ
            { (steps (step s _ _) _ _) → ⊥-elim (¬silent _ s)
            ; (steps _ _ (step s _ _)) → ⊥-elim (¬silent _ s)
            ; (steps done tr done)     → tr
            }
        }
      ; right-inverse-of = λ
          { (steps (step s _ _) _ _) → ⊥-elim (¬silent _ s)
          ; (steps _ _ (step s _ _)) → ⊥-elim (¬silent _ s)
          ; (steps done tr done)     → refl
          }
      }
    ; left-inverse-of = λ _ → refl
    }

  -- If no action is silent, then _[_]⇒̂_ is pointwise isomorphic to
  -- _[_]⟶_ (assuming extensionality).

  ⟶↔⇒̂ : Extensionality lzero lzero →
        (∀ μ → ¬ Silent μ) →
        ∀ {p μ q} → p [ μ ]⟶ q ↔ p [ μ ]⇒̂ q
  ⟶↔⇒̂ ext ¬silent = record
    { surjection = record
      { logical-equivalence = record
        { to   = λ tr → non-silent (¬silent _) (_↔_.to (⟶↔⇒ ¬silent) tr)
        ; from = λ
            { (silent s _)      → ⊥-elim (¬silent _ s)
            ; (non-silent _ tr) → _↔_.from (⟶↔⇒ ¬silent) tr
            }
        }
      ; right-inverse-of = λ
          { (silent s _)      → ⊥-elim (¬silent _ s)
          ; (non-silent _ tr) →
              cong₂ non-silent
                    (ext (⊥-elim ∘ ¬silent _))
                    (_↔_.right-inverse-of (⟶↔⇒ ¬silent) tr)
          }
      }
    ; left-inverse-of = λ _ → refl
    }

  -- Combinators that can be used to add visible type information to
  -- an expression.

  infix -1 step-with-action step-without-action

  step-with-action : ∀ p μ q → p [ μ ]⟶ q → p [ μ ]⟶ q
  step-with-action _ _ _ p⟶q = p⟶q

  step-without-action : ∀ p {μ} q → p [ μ ]⟶ q → p [ μ ]⟶ q
  step-without-action _ _ p⟶q = p⟶q

  syntax step-with-action    p μ q p⟶q = p [ μ ]⟶⟨ p⟶q ⟩ q
  syntax step-without-action p   q p⟶q = p      ⟶⟨ p⟶q ⟩ q

-- Transforms an LTS into one which uses weak transitions as
-- transitions.

weak : LTS → LTS
weak lts = record
  { Proc    = Proc
  ; Label   = Label
  ; Silent  = Silent
  ; silent? = silent?
  ; _[_]⟶_  = _[_]⇒̂_
  }
  where
  open LTS lts

-- If no lts action is silent, then weak lts is equal to lts (assuming
-- extensionality and univalence).

weak≡id :
  Univalence lzero →
  Extensionality lzero (lsuc lzero) →
  ∀ lts →
  (∀ μ → ¬ LTS.Silent lts μ) →
  weak lts ≡ lts
weak≡id univ ext lts ¬silent =
  cong (λ _[_]⟶_ → record
          { Proc    = Proc
          ; Label   = Label
          ; Silent  = Silent
          ; silent? = silent?
          ; _[_]⟶_  = _[_]⟶_
          })
       (ext λ p → ext λ μ → ext λ q →
          p [ μ ]⇒̂ q  ≡⟨ ≃⇒≡ univ $ ↔⇒≃ $ inverse $ ⟶↔⇒̂ (lower-extensionality _ _ ext) ¬silent ⟩∎
          p [ μ ]⟶ q  ∎)
  where
  open LTS lts

-- An LTS with no processes or labels.

empty : LTS
empty = record
  { Proc    = ⊥
  ; Label   = ⊥
  ; Silent  = λ _ → ⊥
  ; silent? = λ _ → no λ ()
  ; _[_]⟶_  = λ ()
  }

-- An LTS with a single process, a single (non-silent) label, and a
-- single transition.

one-loop : LTS
one-loop = record
  { Proc    = ⊤
  ; Label   = ⊤
  ; Silent  = λ _ → ⊥
  ; silent? = λ _ → no λ ()
  ; _[_]⟶_  = λ _ _ _ → ⊤
  }

-- An LTS with two distinct, but bisimilar, processes. There are
-- transitions between the two processes.

two-bisimilar-processes : LTS
two-bisimilar-processes = record
  { Proc    = Bool
  ; Label   = ⊤
  ; Silent  = λ _ → ⊥
  ; silent? = λ _ → no λ ()
  ; _[_]⟶_  = λ _ _ _ → ⊤
  }

-- A parametrised LTS for which bisimilarity is logically equivalent
-- to equality.

bisimilarity⇔equality : Set → LTS
bisimilarity⇔equality A = record
  { Proc    = A
  ; Label   = A
  ; Silent  = λ _ → ⊥
  ; silent? = λ _ → no λ ()
  ; _[_]⟶_  = λ p μ q → p ≡ μ × p ≡ q
  }

-- CCS.

module CCS (Name : Set) where

  ----------------------------------------------------------------------
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

  ----------------------------------------------------------------------
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

  -- A simple corollary.

  names-are-not-inverted :
    ∀ {a P Q} → ¬ (name a · P [ name (co a) ]⟶ Q)
  names-are-not-inverted {a} {P} {Q} =
    name a · P [ name (co a) ]⟶ Q  ↝⟨ ·-only ⟩
    name a ≡ name (co a)           ↝⟨ id≢co ∘ cancel-name ⟩□
    ⊥                              □

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

-- An LTS from Section 6.2.5 in "Enhancements of the bisimulation
-- proof method" by Pous and Sangiorgi.

module 6-2-5 (Name : Set) where

  infixr 12 _·_
  infix   4 _[_]⟶_

  data Proc : Set where
    op  : Proc → Proc
    _·_ : Name → Proc → Proc
    ∅   : Proc

  data _[_]⟶_ : Proc → Name → Proc → Set where
    action : ∀ {a P} → a · P [ a ]⟶ P
    op     : ∀ {a P P′ P″} → P [ a ]⟶ P′ → P′ [ a ]⟶ P″ → op P [ a ]⟶ P″

  6-2-5 : LTS
  6-2-5 = record
    { Proc    = Proc
    ; Label   = Name
    ; Silent  = λ _ → ⊥
    ; silent? = λ _ → no λ ()
    ; _[_]⟶_  = _[_]⟶_
    }

-- The partiality monad. (Some people may prefer to call it the delay
-- monad.)

module Partiality-monad where

  mutual

    data Partial (A : Set) (i : Size) : Set where
      now   : A → Partial A i
      later : Partial′ A i → Partial A i

    record Partial′ (A : Set) (i : Size) : Set where
      coinductive
      field
        force : {j : Size< i} → Partial A j

  -- Transitions.

  infix 4 _[_]⟶_

  data _[_]⟶_ {A : Set} :
              Partial A ∞ → Maybe A → Partial A ∞ → Set where
    now   : ∀ {x} → now x   [ just x  ]⟶ now x
    later : ∀ {x} → later x [ nothing ]⟶ Partial′.force x

  partiality-monad : Set → LTS
  partiality-monad A = record
    { Proc    = Partial A ∞
    ; Label   = Maybe A
    ; Silent  = [ const ⊤ , const ⊥ ]
    ; silent? = [ yes , const (no λ ()) ]
    ; _[_]⟶_  = _[_]⟶_
    }

  -- A direct definition of weak bisimilarity.

  mutual

    infix 4 [_]_≈_ [_]_≈′_

    data [_]_≈_ (i : Size) {A : Set} :
                Partial A ∞ → Partial A ∞ → Set where
      now    : ∀ {x} → [ i ] now x ≈ now x
      later  : ∀ {x y} →
               [ i ] Partial′.force x ≈′ Partial′.force y →
               [ i ] later x ≈ later y
      laterˡ : ∀ {x y} →
               [ i ] Partial′.force x ≈ y →
               [ i ] later x ≈ y
      laterʳ : ∀ {x y} →
               [ i ] x ≈ Partial′.force y →
               [ i ] x ≈ later y

    record [_]_≈′_ (i : Size) {A : Set} (x y : Partial A ∞) : Set where
      coinductive
      field
        force : {j : Size< i} → [ j ] x ≈ y
