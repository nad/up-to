------------------------------------------------------------------------
-- "Equational" reasoning combinator setup
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

open import Labelled-transition-system

-- Note that the module parameter is explicit. If the LTS is not given
-- explicitly, then the use of _[ μ ]⟶_ in the instances below can
-- make it hard for Agda to infer what instance to use.

module Labelled-transition-system.Equational-reasoning-instances
         {ℓ} (lts : LTS ℓ) where

open import Prelude

open import Equational-reasoning

open LTS lts

private

  -- Converts one kind of proof of silence to another kind.

  get : ∀ {μ} → T (silent? μ) → Silent μ
  get {μ} _  with silent? μ
  get {μ} () | no _
  get {μ} _  | yes s = s

instance

  convert⟶ : ∀ {μ} → Convertible _[ μ ]⟶_ _[ μ ]⟶_
  convert⟶ = is-convertible id

  convert⟶⇒ : ∀ {μ} {s : T (silent? μ)} → Convertible _[ μ ]⟶_ _⇒_
  convert⟶⇒ {s = s} = is-convertible (⟶→⇒ (get s))

  convert⟶[]⇒ : ∀ {μ} → Convertible _[ μ ]⟶_ _[ μ ]⇒_
  convert⟶[]⇒ = is-convertible ⟶→[]⇒

  convert⟶⇒̂ : ∀ {μ} → Convertible _[ μ ]⟶_ _[ μ ]⇒̂_
  convert⟶⇒̂ = is-convertible ⟶→⇒̂

  convert⟶⟶̂ : ∀ {μ} → Convertible _[ μ ]⟶_ _[ μ ]⟶̂_
  convert⟶⟶̂ = is-convertible ⟶→⟶̂

  convert⇒ : Convertible _⇒_ _⇒_
  convert⇒ = is-convertible id

  convert⇒⇒̂ : ∀ {μ} {s : T (silent? μ)} → Convertible _⇒_ _[ μ ]⇒̂_
  convert⇒⇒̂ {s = s} = is-convertible (silent (get s))

  convert[]⇒ : ∀ {μ} → Convertible _[ μ ]⇒_ _[ μ ]⇒_
  convert[]⇒ = is-convertible id

  convert[]⇒⇒ : ∀ {μ} {s : T (silent? μ)} → Convertible _[ μ ]⇒_ _⇒_
  convert[]⇒⇒ {s = s} = is-convertible ([]⇒→⇒ (get s))

  convert[]⇒⇒̂ : ∀ {μ} → Convertible _[ μ ]⇒_ _[ μ ]⇒̂_
  convert[]⇒⇒̂ = is-convertible ⇒→⇒̂

  convert⇒̂ : ∀ {μ} → Convertible _[ μ ]⇒̂_ _[ μ ]⇒̂_
  convert⇒̂ = is-convertible id

  convert⇒̂⇒ : ∀ {μ} {s : T (silent? μ)} → Convertible _[ μ ]⇒̂_ _⇒_
  convert⇒̂⇒ {s = s} = is-convertible (⇒̂→⇒ (get s))

  convert⇒̂[]⇒ : ∀ {μ} {¬s : if (silent? μ) then ⊥ else ⊤} →
                Convertible _[ μ ]⇒̂_ _[ μ ]⇒_
  convert⇒̂[]⇒ {μ}       with silent? μ
  convert⇒̂[]⇒ {¬s = ()} | yes _
  convert⇒̂[]⇒           | no ¬s = is-convertible (⇒̂→[]⇒ ¬s)

  convert⟶̂ : ∀ {μ} → Convertible _[ μ ]⟶̂_ _[ μ ]⟶̂_
  convert⟶̂ = is-convertible id

  convert⟶̂⇒ : ∀ {μ} {s : T (silent? μ)} → Convertible _[ μ ]⟶̂_ _⇒_
  convert⟶̂⇒ {s = s} = is-convertible (⟶̂→⇒ (get s))

  convert⟶̂⇒̂ : ∀ {μ} → Convertible _[ μ ]⟶̂_ _[ μ ]⇒̂_
  convert⟶̂⇒̂ = is-convertible ⟶̂→⇒̂

  reflexive⇒ : Reflexive _⇒_
  reflexive⇒ = is-reflexive done

  reflexive⟶̂ : ∀ {μ} {s : T (silent? μ)} → Reflexive _[ μ ]⟶̂_
  reflexive⟶̂ {s = s} = is-reflexive (done (get s))

  reflexive⇒̂ : ∀ {μ} {s : T (silent? μ)} → Reflexive _[ μ ]⇒̂_
  reflexive⇒̂ {s = s} = is-reflexive (silent (get s) done)

  trans⇒ : Transitive _⇒_ _⇒_
  trans⇒ = is-transitive ⇒-transitive

  trans⟶⇒ : ∀ {μ} {s : T (silent? μ)} → Transitive _[ μ ]⟶_ _⇒_
  trans⟶⇒ {s = s} = is-transitive (⇒-transitive ∘ ⟶→⇒ (get s))

  trans⇒̂⇒ : ∀ {μ} {s : T (silent? μ)} → Transitive _[ μ ]⇒̂_ _⇒_
  trans⇒̂⇒ {s = s} = is-transitive (⇒-transitive ∘ ⇒̂→⇒ (get s))

  trans⟶̂⇒ : ∀ {μ} {s : T (silent? μ)} → Transitive _[ μ ]⟶̂_ _⇒_
  trans⟶̂⇒ {s = s} = is-transitive (⇒-transitive ∘ ⟶̂→⇒ (get s))

  trans⇒[]⇒ : ∀ {μ} → Transitive _⇒_ _[ μ ]⇒_
  trans⇒[]⇒ = is-transitive ⇒[]⇒-transitive

  trans⟶[]⇒ : ∀ {μ μ′} {s : T (silent? μ′)} →
              Transitive _[ μ′ ]⟶_ _[ μ ]⇒_
  trans⟶[]⇒ {s = s} = is-transitive (⇒[]⇒-transitive ∘ ⟶→⇒ (get s))

  trans[]⇒[]⇒ : ∀ {μ μ′} {s : T (silent? μ′)} →
                Transitive _[ μ′ ]⇒_ _[ μ ]⇒_
  trans[]⇒[]⇒ {s = s} = is-transitive (⇒[]⇒-transitive ∘ []⇒→⇒ (get s))

  trans⟶̂[]⇒ : ∀ {μ μ′} {s : T (silent? μ′)} →
              Transitive _[ μ′ ]⟶̂_ _[ μ ]⇒_
  trans⟶̂[]⇒ {s = s} = is-transitive (⇒[]⇒-transitive ∘ ⟶̂→⇒ (get s))

  trans⇒⇒̂ : ∀ {μ} → Transitive _⇒_ _[ μ ]⇒̂_
  trans⇒⇒̂ = is-transitive ⇒⇒̂-transitive

  trans⟶⇒̂ : ∀ {μ μ′} {s : T (silent? μ′)} →
              Transitive _[ μ′ ]⟶_ _[ μ ]⇒̂_
  trans⟶⇒̂ {s = s} = is-transitive (⇒⇒̂-transitive ∘ ⟶→⇒ (get s))

  trans[]⇒⇒̂ : ∀ {μ μ′} {s : T (silent? μ′)} →
                Transitive _[ μ′ ]⇒_ _[ μ ]⇒̂_
  trans[]⇒⇒̂ {s = s} = is-transitive (⇒⇒̂-transitive ∘ []⇒→⇒ (get s))

  trans[]⇒̂⇒̂ : ∀ {μ μ′} {s : T (silent? μ′)} →
              Transitive _[ μ′ ]⇒̂_ _[ μ ]⇒̂_
  trans[]⇒̂⇒̂ {s = s} = is-transitive (⇒⇒̂-transitive ∘ ⇒̂→⇒ (get s))

  trans⟶̂⇒̂ : ∀ {μ μ′} {s : T (silent? μ′)} →
              Transitive _[ μ′ ]⟶̂_ _[ μ ]⇒̂_
  trans⟶̂⇒̂ {s = s} = is-transitive (⇒⇒̂-transitive ∘ ⟶̂→⇒ (get s))

  trans′⇒⟶ : ∀ {μ} {s : T (silent? μ)} → Transitive′ _⇒_ _[ μ ]⟶_
  trans′⇒⟶ {s = s} =
    is-transitive (flip (flip ⇒-transitive ∘ ⟶→⇒ (get s)))

  trans′⇒[]⇒ : ∀ {μ} {s : T (silent? μ)} → Transitive′ _⇒_ _[ μ ]⇒_
  trans′⇒[]⇒ {s = s} =
    is-transitive (flip (flip ⇒-transitive ∘ []⇒→⇒ (get s)))

  trans′⇒⇒̂ : ∀ {μ} {s : T (silent? μ)} → Transitive′ _⇒_ _[ μ ]⇒̂_
  trans′⇒⇒̂ {s = s} =
    is-transitive (flip (flip ⇒-transitive ∘ ⇒̂→⇒ (get s)))

  trans′⇒⟶̂ : ∀ {μ} {s : T (silent? μ)} → Transitive′ _⇒_ _[ μ ]⟶̂_
  trans′⇒⟶̂ {s = s} =
    is-transitive (flip (flip ⇒-transitive ∘ ⟶̂→⇒ (get s)))

  trans′[]⇒⟶ : ∀ {μ μ′} {s : T (silent? μ′)} →
               Transitive′ _[ μ ]⇒_ _[ μ′ ]⟶_
  trans′[]⇒⟶ {s = s} =
    is-transitive (flip (flip []⇒⇒-transitive ∘ ⟶→⇒ (get s)))

  trans′[]⇒⇒ : ∀ {μ} → Transitive′ _[ μ ]⇒_ _⇒_
  trans′[]⇒⇒ = is-transitive []⇒⇒-transitive

  trans′[]⇒[]⇒ : ∀ {μ μ′} {s : T (silent? μ′)} →
                 Transitive′ _[ μ ]⇒_ _[ μ′ ]⇒_
  trans′[]⇒[]⇒ {s = s} =
    is-transitive (flip (flip []⇒⇒-transitive ∘ []⇒→⇒ (get s)))

  trans′[]⇒[]⇒̂ : ∀ {μ μ′} {s : T (silent? μ′)} →
                 Transitive′ _[ μ ]⇒_ _[ μ′ ]⇒̂_
  trans′[]⇒[]⇒̂ {s = s} =
    is-transitive (flip (flip []⇒⇒-transitive ∘ ⇒̂→⇒ (get s)))

  trans′[]⇒⟶̂ : ∀ {μ μ′} {s : T (silent? μ′)} →
               Transitive′ _[ μ ]⇒_ _[ μ′ ]⟶̂_
  trans′[]⇒⟶̂ {s = s} =
    is-transitive (flip (flip []⇒⇒-transitive ∘ ⟶̂→⇒ (get s)))

  trans′⇒̂⟶ : ∀ {μ μ′} {s : T (silent? μ′)} →
             Transitive′ _[ μ ]⇒̂_ _[ μ′ ]⟶_
  trans′⇒̂⟶ {s = s} =
    is-transitive (flip (flip ⇒̂⇒-transitive ∘ ⟶→⇒ (get s)))

  trans′⇒̂⇒ : ∀ {μ} → Transitive′ _[ μ ]⇒̂_ _⇒_
  trans′⇒̂⇒ = is-transitive ⇒̂⇒-transitive

  trans′⇒̂[]⇒ : ∀ {μ μ′} {s : T (silent? μ′)} →
               Transitive′ _[ μ ]⇒̂_ _[ μ′ ]⇒_
  trans′⇒̂[]⇒ {s = s} =
    is-transitive (flip (flip ⇒̂⇒-transitive ∘ []⇒→⇒ (get s)))

  trans′⇒̂⇒̂ : ∀ {μ μ′} {s : T (silent? μ′)} →
             Transitive′ _[ μ ]⇒̂_ _[ μ′ ]⇒̂_
  trans′⇒̂⇒̂ {s = s} =
    is-transitive (flip (flip ⇒̂⇒-transitive ∘ ⇒̂→⇒ (get s)))

  trans′⇒̂⟶̂ : ∀ {μ μ′} {s : T (silent? μ′)} →
             Transitive′ _[ μ ]⇒̂_ _[ μ′ ]⟶̂_
  trans′⇒̂⟶̂ {s = s} =
    is-transitive (flip (flip ⇒̂⇒-transitive ∘ ⟶̂→⇒ (get s)))
