------------------------------------------------------------------------
-- Labelled transition systems
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module Labelled-transition-system where

open import Equality.Propositional
import Logical-equivalence
open import Prelude

open import Bijection equality-with-J using (_↔_)
open import Equivalence equality-with-J using (↔⇒≃)
open import Extensionality equality-with-J
open import Function-universe equality-with-J hiding (id; _∘_)
open import Univalence-axiom equality-with-J

-- Labelled transition systems were perhaps first defined by Robert M.
-- Keller (https://doi.org/10.1145/360248.360251). The definition
-- below is a variant with a field "is-silent", added by me.
--
-- I don't know who first came up with the concept of a weak
-- transition. The definitions of _⇒_, _[_]⇒_, _[_]⇒̂_ and _[_]⟶̂_ below
-- are based on definitions in "Enhancements of the bisimulation proof
-- method" by Pous and Sangiorgi.

record LTS ℓ : Type (lsuc ℓ) where
  infix 4 _[_]⟶_ _⇒_ _[_]⇒_ _[_]⇒̂_ _[_]⟶̂_
  field
    -- Processes.
    Proc : Type ℓ

    -- Labels.
    Label : Type ℓ

    -- Transitions.
    _[_]⟶_ : Proc → Label → Proc → Type ℓ

    -- Is the label silent?
    is-silent : Label → Bool

  -- Is the label silent?

  Silent : Label → Type
  Silent μ with is-silent μ
  ... | true  = ⊤
  ... | false = ⊥

  -- Silence can be decided.

  silent? : ∀ μ → Dec (Silent μ)
  silent? μ with is-silent μ
  ... | true  = yes _
  ... | false = no id

  -- Sequences of zero or more silent transitions.

  data _⇒_ : Proc → Proc → Type ℓ where
    done : ∀ {p} → p ⇒ p
    step : ∀ {p q r μ} → Silent μ → p [ μ ]⟶ q → q ⇒ r → p ⇒ r

  -- Weak transitions (one kind).

  data _[_]⇒_ (p : Proc) (μ : Label) (q : Proc) : Type ℓ where
    steps : ∀ {p′ q′} → p ⇒ p′ → p′ [ μ ]⟶ q′ → q′ ⇒ q → p [ μ ]⇒ q

  -- Weak transitions (another kind).

  data _[_]⇒̂_ (p : Proc) (μ : Label) (q : Proc) : Type ℓ where
    silent     : Silent μ → p ⇒ q → p [ μ ]⇒̂ q
    non-silent : ¬ Silent μ → p [ μ ]⇒ q → p [ μ ]⇒̂ q

  -- Weak transitions (yet another kind).

  data _[_]⟶̂_ (p : Proc) (μ : Label) : Proc → Type ℓ where
    done : Silent μ → p [ μ ]⟶̂ p
    step : ∀ {q} → p [ μ ]⟶ q → p [ μ ]⟶̂ q

  -- Functions that can be used to aid the instance resolution
  -- mechanism.

  infix -2 ⟶:_ ⇒:_ []⇒:_ ⇒̂:_ ⟶̂:_

  ⟶:_ : ∀ {p μ q} → p [ μ ]⟶ q → p [ μ ]⟶ q
  ⟶:_ = id

  ⇒:_ : ∀ {p q} → p ⇒ q → p ⇒ q
  ⇒:_ = id

  []⇒:_ : ∀ {p μ q} → p [ μ ]⇒ q → p [ μ ]⇒ q
  []⇒:_ = id

  ⇒̂:_ : ∀ {p μ q} → p [ μ ]⇒̂ q → p [ μ ]⇒̂ q
  ⇒̂:_ = id

  ⟶̂:_ : ∀ {p μ q} → p [ μ ]⟶̂ q → p [ μ ]⟶̂ q
  ⟶̂:_ = id

  -- An "equational" reasoning combinator that is not subsumed by the
  -- combinators in Equational-reasoning, because the types of the two
  -- main arguments and the result use three different relations.

  infixr -2 ⟶⇒→[]⇒

  ⟶⇒→[]⇒ : ∀ p μ {q r} → p [ μ ]⟶ q → q ⇒ r → p [ μ ]⇒ r
  ⟶⇒→[]⇒ _ _ = steps done

  syntax ⟶⇒→[]⇒ p μ p⟶q q⇒r = p [ μ ]⇒⟨ p⟶q ⟩ q⇒r

  -- Combinators that can be used to add visible type information to
  -- an expression.

  infix -1 step-with-action step-without-action

  step-with-action : ∀ p μ q → p [ μ ]⟶ q → p [ μ ]⟶ q
  step-with-action _ _ _ p⟶q = p⟶q

  step-without-action : ∀ p {μ} q → p [ μ ]⟶ q → p [ μ ]⟶ q
  step-without-action _ _ p⟶q = p⟶q

  syntax step-with-action    p μ q p⟶q = p [ μ ]⟶⟨ p⟶q ⟩ q
  syntax step-without-action p   q p⟶q = p      ⟶⟨ p⟶q ⟩ q

  -- Regular transitions can (sometimes) be turned into weak ones.

  ⟶→⇒ : ∀ {p μ q} → Silent μ → p [ μ ]⟶ q → p ⇒ q
  ⟶→⇒ s tr = step s tr done

  ⟶→[]⇒ : ∀ {p μ q} → p [ μ ]⟶ q → p [ μ ]⇒ q
  ⟶→[]⇒ tr = steps done tr done

  ⟶→⇒̂ : ∀ {p μ q} → p [ μ ]⟶ q → p [ μ ]⇒̂ q
  ⟶→⇒̂ {μ = μ} tr with silent? μ
  ... | yes s = silent s (⟶→⇒ s tr)
  ... | no ¬s = non-silent ¬s (⟶→[]⇒ tr)

  ⟶→⟶̂ : ∀ {p μ q} → p [ μ ]⟶ q → p [ μ ]⟶̂ q
  ⟶→⟶̂ = step

  -- Several transitivity-like properties.

  ⇒-transitive : ∀ {p q r} → p ⇒ q → q ⇒ r → p ⇒ r
  ⇒-transitive done             p⇒q = p⇒q
  ⇒-transitive (step s p⟶q q⇒r) r⇒s = step s p⟶q (⇒-transitive q⇒r r⇒s)

  ⇒[]⇒-transitive : ∀ {p q r μ} → p ⇒ q → q [ μ ]⇒ r → p [ μ ]⇒ r
  ⇒[]⇒-transitive p⇒q (steps q⇒r r⟶s s⇒t) =
    steps (⇒-transitive p⇒q q⇒r) r⟶s s⇒t

  []⇒⇒-transitive : ∀ {p q r μ} → p [ μ ]⇒ q → q ⇒ r → p [ μ ]⇒ r
  []⇒⇒-transitive (steps p⇒q q⟶r r⇒s) s⇒t =
    steps p⇒q q⟶r (⇒-transitive r⇒s s⇒t)

  ⇒⇒̂-transitive : ∀ {p q r μ} → p ⇒ q → q [ μ ]⇒̂ r → p [ μ ]⇒̂ r
  ⇒⇒̂-transitive p⇒q (silent s q⇒r) = silent s (⇒-transitive p⇒q q⇒r)
  ⇒⇒̂-transitive p⇒q (non-silent ¬s q⇒r) =
    non-silent ¬s (⇒[]⇒-transitive p⇒q q⇒r)

  ⇒̂⇒-transitive : ∀ {p q r μ} → p [ μ ]⇒̂ q → q ⇒ r → p [ μ ]⇒̂ r
  ⇒̂⇒-transitive (silent s p⇒q) q⇒r = silent s (⇒-transitive p⇒q q⇒r)
  ⇒̂⇒-transitive (non-silent ¬s p⇒q) q⇒r =
    non-silent ¬s ([]⇒⇒-transitive p⇒q q⇒r)

  -- More conversion functions.

  []⇒→⇒ : ∀ {p q μ} → Silent μ → p [ μ ]⇒ q → p ⇒ q
  []⇒→⇒ s (steps p⇒p′ p′⟶p″ p″⇒p‴) =
    ⇒-transitive p⇒p′ (step s p′⟶p″ p″⇒p‴)

  ⇒̂→⇒ : ∀ {p q μ} → Silent μ → p [ μ ]⇒̂ q → p ⇒ q
  ⇒̂→⇒ s (silent _ p⇒q)    = p⇒q
  ⇒̂→⇒ s (non-silent ¬s _) = ⊥-elim (¬s s)

  ⇒→⇒̂ : ∀ {p q μ} → p [ μ ]⇒ q → p [ μ ]⇒̂ q
  ⇒→⇒̂ {μ = μ} tr with silent? μ
  ... | yes s = silent s ([]⇒→⇒ s tr)
  ... | no ¬s = non-silent ¬s tr

  ⇒̂→[]⇒ : ∀ {p q μ} → ¬ Silent μ → p [ μ ]⇒̂ q → p [ μ ]⇒ q
  ⇒̂→[]⇒ ¬s (silent s _)      = ⊥-elim (¬s s)
  ⇒̂→[]⇒ _  (non-silent _ tr) = tr

  ⟶̂→⇒̂ : ∀ {p μ q} → p [ μ ]⟶̂ q → p [ μ ]⇒̂ q
  ⟶̂→⇒̂ (done s)  = silent s done
  ⟶̂→⇒̂ (step tr) = ⟶→⇒̂ tr

  ⟶̂→⇒ : ∀ {p q μ} → Silent μ → p [ μ ]⟶̂ q → p ⇒ q
  ⟶̂→⇒ s = ⇒̂→⇒ s ∘ ⟶̂→⇒̂

  -- Lemmas that can be used to show that relations are weak
  -- simulations of various kinds.

  module _
    {ℓ}
    {_%_ _%′_ : Proc → Proc → Type ℓ}
    {_[_]%_ : Proc → Label → Proc → Type ℓ}
    (left-to-right :
       ∀ {p q} → p % q → ∀ {p′ μ} →
       p [ μ ]⟶ p′ → ∃ λ q′ → q [ μ ]% q′ × p′ %′ q′)
    (%′⇒% : ∀ {p q} → p %′ q → p % q)
    (%⇒⇒ : ∀ {p p′ μ} → Silent μ → p [ μ ]% p′ → p ⇒ p′)
    where

    is-weak⇒ :
      ∀ {p p′ q} →
      p % q → p ⇒ p′ →
      ∃ λ q′ → q ⇒ q′ × (p′ % q′)
    is-weak⇒ p%q done                = _ , done , p%q
    is-weak⇒ p%q (step s p⟶p′ p′⇒p″) =
      let q′ , q%q′  , p′%′q′ = left-to-right p%q p⟶p′
          q″ , q′⇒q″ , p″%q″  = is-weak⇒ (%′⇒% p′%′q′) p′⇒p″
      in q″ , ⇒-transitive (%⇒⇒ s q%q′) q′⇒q″ , p″%q″

    is-weak[]⇒ :
      ∀ {p p′ q μ} →
      (∀ {p p′} → p [ μ ]% p′ → p [ μ ]⇒ p′) →
      p % q → p [ μ ]⇒ p′ →
      ∃ λ q′ → q [ μ ]⇒ q′ × (p′ % q′)
    is-weak[]⇒ %⇒[]⇒ p%q (steps p⇒p′ p′⟶p″ p″⇒p‴) =
      let q′ , q⇒q′  , p′%q′  = is-weak⇒ p%q p⇒p′
          q″ , q′%q″ , p″%′q″ = left-to-right p′%q′ p′⟶p″
          q‴ , q″⇒q‴ , p‴%q‴  = is-weak⇒ (%′⇒% p″%′q″) p″⇒p‴
      in q‴
       , ⇒[]⇒-transitive q⇒q′ ([]⇒⇒-transitive (%⇒[]⇒ q′%q″) q″⇒q‴)
       , p‴%q‴

    is-weak⇒̂ :
      ∀ {p p′ q μ} →
      (∀ {p p′} → p [ μ ]% p′ → p [ μ ]⇒̂ p′) →
      p % q → p [ μ ]⇒̂ p′ →
      ∃ λ q′ → q [ μ ]⇒̂ q′ × (p′ % q′)
    is-weak⇒̂ _ q%r (silent s q⇒q′) =
      Σ-map id (Σ-map (silent s) id) (is-weak⇒ q%r q⇒q′)
    is-weak⇒̂ %⇒⇒̂ q%r (non-silent ¬s q⇒q′) =
      Σ-map id (Σ-map ⇒→⇒̂ id) (is-weak[]⇒ (⇒̂→[]⇒ ¬s ∘ %⇒⇒̂) q%r q⇒q′)

  -- If no action is silent, then _[_]⇒_ is pointwise isomorphic to
  -- _[_]⟶_.

  ⟶↔⇒ : (∀ μ → ¬ Silent μ) →
        ∀ {p μ q} → p [ μ ]⟶ q ↔ p [ μ ]⇒ q
  ⟶↔⇒ ¬silent = record
    { surjection = record
      { logical-equivalence = record
        { to   = ⟶→[]⇒
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

  -- If no action is silent, then _[_]⇒̂_ is pointwise logically
  -- equivalent to _[_]⟶_, and in the presence of extensionality they
  -- are pointwise isomorphic.

  ⟶↔⇒̂ : ∀ {k} →
        Extensionality? k lzero lzero →
        (∀ μ → ¬ Silent μ) →
        ∀ {p μ q} → p [ μ ]⟶ q ↝[ k ] p [ μ ]⇒̂ q
  ⟶↔⇒̂ ext ¬silent = generalise-ext?
    ⟶⇔⇒̂
    (λ ext →
         (λ { (silent s _)      → ⊥-elim (¬silent _ s)
            ; (non-silent _ tr) →
                cong₂ non-silent
                      (apply-ext ext (⊥-elim ∘ ¬silent _))
                      (_↔_.right-inverse-of (⟶↔⇒ ¬silent) tr)
            })
       , (λ _ → refl))
    ext
    where
    ⟶⇔⇒̂ = record
      { to   = λ tr → non-silent (¬silent _) (_↔_.to (⟶↔⇒ ¬silent) tr)
      ; from = λ
          { (silent s _)      → ⊥-elim (¬silent _ s)
          ; (non-silent _ tr) → _↔_.from (⟶↔⇒ ¬silent) tr
          }
      }

  -- Map-like functions.

  map-⇒′ :
    {F : Proc → Proc} →
    (∀ {p p′ μ} → Silent μ → p [ μ ]⟶ p′ → F p [ μ ]⟶ F p′) →
    ∀ {p p′} → p ⇒ p′ → F p ⇒ F p′
  map-⇒′ f done                = done
  map-⇒′ f (step s p⟶p′ p′⇒p″) =
    step s (f s p⟶p′) (map-⇒′ f p′⇒p″)

  map-⇒ :
    {F : Proc → Proc} →
    (∀ {p p′ μ} → p [ μ ]⟶ p′ → F p [ μ ]⟶ F p′) →
    ∀ {p p′} → p ⇒ p′ → F p ⇒ F p′
  map-⇒ f = map-⇒′ (λ _ → f)

  map-[]⇒′ :
    ∀ {μ} {F : Proc → Proc} →
    (∀ {p p′ μ} → Silent μ → p [ μ ]⟶ p′ → F p [ μ ]⟶ F p′) →
    (∀ {p p′} → p [ μ ]⟶ p′ → F p [ μ ]⟶ F p′) →
    ∀ {p p′} → p [ μ ]⇒ p′ → F p [ μ ]⇒ F p′
  map-[]⇒′ f g (steps p⇒p′ p′⟶p″ p″⇒p‴) =
    steps (map-⇒′ f p⇒p′) (g p′⟶p″) (map-⇒′ f p″⇒p‴)

  map-[]⇒ :
    {F : Proc → Proc} →
    (∀ {p p′ μ} → p [ μ ]⟶ p′ → F p [ μ ]⟶ F p′) →
    ∀ {p p′ μ} → p [ μ ]⇒ p′ → F p [ μ ]⇒ F p′
  map-[]⇒ f = map-[]⇒′ (λ _ → f) f

  map-⇒̂′ :
    ∀ {μ} {F : Proc → Proc} →
    (∀ {p p′ μ} → Silent μ → p [ μ ]⟶ p′ → F p [ μ ]⟶ F p′) →
    (∀ {p p′} → p [ μ ]⟶ p′ → F p [ μ ]⟶ F p′) →
    ∀ {p p′} → p [ μ ]⇒̂ p′ → F p [ μ ]⇒̂ F p′
  map-⇒̂′ f g (silent s p⇒p′)      = silent s (map-⇒′ f p⇒p′)
  map-⇒̂′ f g (non-silent ¬s p⇒p′) = non-silent ¬s (map-[]⇒′ f g p⇒p′)

  map-⇒̂ :
    {F : Proc → Proc} →
    (∀ {p p′ μ} → p [ μ ]⟶ p′ → F p [ μ ]⟶ F p′) →
    ∀ {p p′ μ} → p [ μ ]⇒̂ p′ → F p [ μ ]⇒̂ F p′
  map-⇒̂ f = map-⇒̂′ (λ _ → f) f

  map-⟶̂ :
    ∀ {μ p p′} {F : Proc → Proc} →
    (p [ μ ]⟶ p′ → F p [ μ ]⟶ F p′) →
    p [ μ ]⟶̂ p′ → F p [ μ ]⟶̂ F p′
  map-⟶̂ f (done s)    = done s
  map-⟶̂ f (step p⟶p′) = step (f p⟶p′)

  -- Zip-like functions.

  module _
    {F : Proc → Proc → Proc}
    (f : ∀ {p p′ q μ} → p [ μ ]⟶ p′ → F p q [ μ ]⟶ F p′ q)
    (g : ∀ {p q q′ μ} → q [ μ ]⟶ q′ → F p q [ μ ]⟶ F p q′)
    where

    zip-⇒ : ∀ {p p′ q q′} → p ⇒ p′ → q ⇒ q′ → F p q ⇒ F p′ q′
    zip-⇒ done done                = done
    zip-⇒ done (step s q⟶q′ q′⇒q″) = step s (g q⟶q′) (zip-⇒ done q′⇒q″)
    zip-⇒ (step s p⟶p′ p′⇒p″) tr   = step s (f p⟶p′) (zip-⇒ p′⇒p″ tr)

    zip-[]⇒ˡ′ :
      ∀ {p p′ q q′ μ₁ μ₃} →
      (∀ {p p′ q} → p [ μ₁ ]⟶ p′ → F p q [ μ₃ ]⟶ F p′ q) →
      p [ μ₁ ]⇒ p′ → q ⇒ q′ → F p q [ μ₃ ]⇒ F p′ q′
    zip-[]⇒ˡ′ h (steps p⇒p′ p′⟶p″ p″⇒p‴) q⇒q′ =
      steps (zip-⇒ p⇒p′ q⇒q′) (h p′⟶p″) (zip-⇒ p″⇒p‴ done)

    zip-[]⇒ˡ : ∀ {p p′ q q′ μ} →
               p [ μ ]⇒ p′ → q ⇒ q′ → F p q [ μ ]⇒ F p′ q′
    zip-[]⇒ˡ = zip-[]⇒ˡ′ f

    zip-[]⇒ʳ′ :
      ∀ {p p′ q q′ μ₂ μ₃} →
      (∀ {p q q′} → q [ μ₂ ]⟶ q′ → F p q [ μ₃ ]⟶ F p q′) →
      p ⇒ p′ → q [ μ₂ ]⇒ q′ → F p q [ μ₃ ]⇒ F p′ q′
    zip-[]⇒ʳ′ h p⇒p′ (steps q⇒q′ q′⟶q″ q″⇒q‴) =
      steps (zip-⇒ p⇒p′ q⇒q′) (h q′⟶q″) (zip-⇒ done q″⇒q‴)

    zip-[]⇒ʳ : ∀ {p p′ q q′ μ} →
               p ⇒ p′ → q [ μ ]⇒ q′ → F p q [ μ ]⇒ F p′ q′
    zip-[]⇒ʳ = zip-[]⇒ʳ′ g

    zip-[]⇒ :
      ∀ {μ₁ μ₂ μ₃} →
      (∀ {p p′ q q′} →
       p [ μ₁ ]⟶ p′ → q [ μ₂ ]⟶ q′ → F p q [ μ₃ ]⟶ F p′ q′) →
      ∀ {p p′ q q′} →
      p [ μ₁ ]⇒ p′ → q [ μ₂ ]⇒ q′ → F p q [ μ₃ ]⇒ F p′ q′
    zip-[]⇒ h (steps p⇒p′ p′⟶p″ p″⇒p‴) (steps q⇒q′ q′⟶q″ q″⇒q‴) =
      steps (zip-⇒ p⇒p′ q⇒q′) (h p′⟶p″ q′⟶q″) (zip-⇒ p″⇒p‴ q″⇒q‴)

    zip-⇒̂ :
      ∀ {μ₁ μ₂ μ₃} →
      (Silent μ₁ → Silent μ₂ → Silent μ₃) →
      (∀ {p p′ q} → p [ μ₁ ]⟶ p′ → Silent μ₂ → F p q [ μ₃ ]⟶ F p′ q) →
      (∀ {p q q′} → Silent μ₁ → q [ μ₂ ]⟶ q′ → F p q [ μ₃ ]⟶ F p q′) →
      (∀ {p p′ q q′} →
       p [ μ₁ ]⟶ p′ → q [ μ₂ ]⟶ q′ → F p q [ μ₃ ]⟶ F p′ q′) →
      ∀ {p p′ q q′} →
      p [ μ₁ ]⇒̂ p′ → q [ μ₂ ]⇒̂ q′ → F p q [ μ₃ ]⇒̂ F p′ q′
    zip-⇒̂ fs hˡ hʳ h = λ where
      (silent s₁ tr₁)      (silent s₂ tr₂)      → silent (fs s₁ s₂) (zip-⇒ tr₁ tr₂)
      (silent s₁ tr₁)      (non-silent ¬s₂ tr₂) → ⇒→⇒̂ (zip-[]⇒ʳ′ (hʳ s₁)      tr₁ tr₂)
      (non-silent ¬s₁ tr₁) (silent s₂ tr₂)      → ⇒→⇒̂ (zip-[]⇒ˡ′ (flip hˡ s₂) tr₁ tr₂)
      (non-silent ¬s₁ tr₁) (non-silent ¬s₂ tr₂) → ⇒→⇒̂ (zip-[]⇒   h            tr₁ tr₂)

  zip-⟶̂ :
    ∀ {F : Proc → Proc → Proc} {μ₁ μ₂ μ₃} →
    (Silent μ₁ → Silent μ₂ → Silent μ₃) →
    (∀ {p p′ q} → p [ μ₁ ]⟶ p′ → Silent μ₂ → F p q [ μ₃ ]⟶ F p′ q) →
    (∀ {p q q′} → Silent μ₁ → q [ μ₂ ]⟶ q′ → F p q [ μ₃ ]⟶ F p q′) →
    (∀ {p p′ q q′} →
     p [ μ₁ ]⟶ p′ → q [ μ₂ ]⟶ q′ → F p q [ μ₃ ]⟶ F p′ q′) →
    ∀ {p p′ q q′} → p [ μ₁ ]⟶̂ p′ → q [ μ₂ ]⟶̂ q′ → F p q [ μ₃ ]⟶̂ F p′ q′
  zip-⟶̂ s f g h (done s₁)   (done s₂)   = done (s s₁ s₂)
  zip-⟶̂ s f g h (done s₁)   (step q⟶q′) = step (g s₁ q⟶q′)
  zip-⟶̂ s f g h (step p⟶p′) (done s₂)   = step (f p⟶p′ s₂)
  zip-⟶̂ s f g h (step p⟶p′) (step q⟶q′) = step (h p⟶p′ q⟶q′)

-- Transforms an LTS into one which uses weak transitions as
-- transitions.

weak : ∀ {ℓ} → LTS ℓ → LTS ℓ
weak lts = record
  { Proc      = Proc
  ; Label     = Label
  ; _[_]⟶_    = _[_]⇒̂_
  ; is-silent = is-silent
  }
  where
  open LTS lts

-- If no lts action is silent, then weak lts is equal to lts (assuming
-- extensionality and univalence).

weak≡id :
  ∀ {ℓ} →
  Extensionality ℓ (lsuc ℓ) →
  Univalence ℓ →
  (lts : LTS ℓ) →
  (∀ μ → ¬ LTS.Silent lts μ) →
  weak lts ≡ lts
weak≡id ext univ lts ¬silent =
  cong (λ _[_]⟶_ → record
          { Proc      = Proc
          ; Label     = Label
          ; _[_]⟶_    = _[_]⟶_
          ; is-silent = is-silent
          })
       (apply-ext ext λ p → apply-ext ext λ μ → apply-ext ext λ q →
          p [ μ ]⇒̂ q  ≡⟨ ≃⇒≡ univ $ ↔⇒≃ $ inverse $ ⟶↔⇒̂ (lower-extensionality _ _ ext) ¬silent ⟩∎
          p [ μ ]⟶ q  ∎)
  where
  open LTS lts

-- An LTS with no processes or labels.

empty : LTS lzero
empty = record
  { Proc      = ⊥
  ; Label     = ⊥
  ; _[_]⟶_    = λ ()
  ; is-silent = λ ()
  }

-- An LTS with a single process, a single (non-silent) label, and a
-- single transition.

one-loop : LTS lzero
one-loop = record
  { Proc      = ⊤
  ; Label     = ⊤
  ; _[_]⟶_    = λ _ _ _ → ⊤
  ; is-silent = λ _ → false
  }

-- An LTS with two distinct, but bisimilar, processes. There are
-- transitions between the two processes.

two-bisimilar-processes : LTS lzero
two-bisimilar-processes = record
  { Proc      = Bool
  ; Label     = ⊤
  ; _[_]⟶_    = λ _ _ _ → ⊤
  ; is-silent = λ _ → false
  }

-- A parametrised LTS for which bisimilarity is logically equivalent
-- to equality.

bisimilarity⇔equality : ∀ {ℓ} → Type ℓ → LTS ℓ
bisimilarity⇔equality A = record
  { Proc      = A
  ; Label     = A
  ; _[_]⟶_    = λ p μ q → p ≡ μ × p ≡ q
  ; is-silent = λ _ → false
  }
