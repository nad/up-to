------------------------------------------------------------------------
-- Indexed containers
------------------------------------------------------------------------

-- Roughly following "Indexed containers" by Altenkirch, Ghani,
-- Hancock, McBride and Morris (JFP, 2015).

{-# OPTIONS --without-K #-}

module Indexed-container where

open import Equality.Propositional hiding (Extensionality)
open import Interval using (ext)
open import Prelude

open import Bijection equality-with-J as Bijection using (_↔_)
import Equivalence equality-with-J as Eq
open import Function-universe equality-with-J hiding (id; _∘_)
open import Univalence-axiom equality-with-J

------------------------------------------------------------------------
-- Containers

-- Singly indexed containers.

record Container₁ {ℓ} (I : Set ℓ) : Set (lsuc ℓ) where
  constructor _◁₁_
  field
    Shape    : Set ℓ
    Position : Shape → I → Set ℓ

-- Doubly indexed containers.

Container : ∀ {ℓ} → Set ℓ → Set ℓ → Set (lsuc ℓ)
Container I O = O → Container₁ I

-- A "constructor".

_◁_ : ∀ {ℓ} {I O : Set ℓ} →
      (S : O → Set ℓ) → (∀ {o} → S o → I → Set ℓ) → Container I O
(S ◁ P) o = S o ◁₁ P

-- Some "projections".

module Container {ℓ} {I O : Set ℓ} (C : Container I O) where

  Shape : O → Set ℓ
  Shape = Container₁.Shape ∘ C

  Position : ∀ {o} → Shape o → I → Set ℓ
  Position = Container₁.Position (C _)

-- Index-preserving functions.

infix 4 _→⋆_

_→⋆_ : ∀ {i ℓ₁ ℓ₂} {I : Set i} →
       (I → Set ℓ₁) → (I → Set ℓ₂) → Set (i ⊔ ℓ₁ ⊔ ℓ₂)
A →⋆ B = ∀ {i} → A i → B i

-- Interpretations of containers.

⟦_⟧₁ : ∀ {ℓ₁ ℓ₂} {I : Set ℓ₁} →
       Container₁ I → (I → Set ℓ₂) → Set (ℓ₁ ⊔ ℓ₂)
⟦ S ◁₁ P ⟧₁ Q = ∃ λ (s : S) → P s →⋆ Q

⟦_⟧ : ∀ {ℓ₁ ℓ₂} {I O : Set ℓ₁} →
      Container I O → (I → Set ℓ₂) → (O → Set (ℓ₁ ⊔ ℓ₂))
⟦ C ⟧ Q o = ⟦ C o ⟧₁ Q

-- A variant of a special case of ⟦_⟧. Can be used when both index
-- sets are sigma types.

⟦_⟧₂ : ∀ {ℓ₁ ℓ₂} {I₁ O₁ : Set ℓ₁} {I₂ : I₁ → Set ℓ₁} {O₂ : O₁ → Set ℓ₁} →
       Container (Σ I₁ I₂) (Σ O₁ O₂) →
       ((i₁ : I₁) → I₂ i₁ → Set ℓ₂) →
       ((o₁ : O₁) → O₂ o₁ → Set (ℓ₁ ⊔ ℓ₂))
⟦ C ⟧₂ = curry ∘ ⟦ C ⟧ ∘ uncurry

-- Map functions.

map₁ : ∀ {ℓ₁ ℓ₂} {I : Set ℓ₁} {C : Container₁ I} {A B : I → Set ℓ₂} →
       A →⋆ B → ⟦ C ⟧₁ A → ⟦ C ⟧₁ B
map₁ f = Σ-map id (λ g {_} → f ∘ g {i = _})

map : ∀ {ℓ₁ ℓ₂} {I O : Set ℓ₁} (C : Container I O) {A B : I → Set ℓ₂} →
      A →⋆ B → ⟦ C ⟧ A →⋆ ⟦ C ⟧ B
map _ f = map₁ f

------------------------------------------------------------------------
-- Least fixpoints

mutual

  -- The least fixpoint of an indexed "endocontainer", expressed using
  -- sized types.

  μ : ∀ {ℓ} {I : Set ℓ} → Container I I → Size → I → Set ℓ
  μ C i = ⟦ C ⟧ (μ′ C i)

  data μ′ {ℓ} {I : Set ℓ}
          (C : Container I I) (i : Size) (o : I) : Set ℓ where
    ⟨_⟩ : {j : Size< i} → μ C j o → μ′ C i o

-- An inverse of ⟨_⟩ (for fully defined values).

⟨_⟩⁻¹ :
  ∀ {ℓ} {I : Set ℓ} {C : Container I I} →
  μ′ C ∞ →⋆ μ C ∞
⟨ ⟨ x ⟩ ⟩⁻¹ = x

-- The least fixpoint is a post-fixpoint.

μ-out :
  ∀ {ℓ} {I : Set ℓ} {C : Container I I} →
  μ C ∞ →⋆ ⟦ C ⟧ (μ C ∞)
μ-out {C = C} = map C ⟨_⟩⁻¹

-- The greatest fixpoint is a pre-fixpoint.

μ-in :
  ∀ {ℓ} {I : Set ℓ} {C : Container I I} →
  ⟦ C ⟧ (μ C ∞) →⋆ μ C ∞
μ-in {C = C} = map C ⟨_⟩

mutual

  -- The least fixpoint is smaller than or equal to every
  -- pre-fixpoint.

  fold :
    ∀ {ℓ} {I : Set ℓ} (C : Container I I) {X : I → Set ℓ} →
    (⟦ C ⟧ X →⋆ X) →
    ∀ {i} → μ C i →⋆ X
  fold C f x = f (map C (fold′ C f) x)

  fold′ :
    ∀ {ℓ} {I : Set ℓ} (C : Container I I) {X : I → Set ℓ} →
    (⟦ C ⟧ X →⋆ X) →
    ∀ {i} → μ′ C i →⋆ X
  fold′ C f ⟨ x ⟩ = fold C f x

------------------------------------------------------------------------
-- Greatest fixpoints

mutual

  -- The greatest fixpoint of an indexed "endocontainer", expressed
  -- using sized types.

  ν : ∀ {ℓ} {I : Set ℓ} → Container I I → Size → I → Set ℓ
  ν C i = ⟦ C ⟧ (ν′ C i)

  record ν′ {ℓ} {I : Set ℓ}
            (C : Container I I) (i : Size) (o : I) : Set ℓ where
    coinductive
    field
      force : {j : Size< i} → ν C j o

open ν′ public

-- The greatest fixpoint is a post-fixpoint.

ν-out :
  ∀ {ℓ} {I : Set ℓ} {C : Container I I} →
  ν C ∞ →⋆ ⟦ C ⟧ (ν C ∞)
ν-out {C = C} = map C (λ x → force x)

-- The greatest fixpoint is a pre-fixpoint.

ν-in :
  ∀ {ℓ} {I : Set ℓ} (C : Container I I) →
  ⟦ C ⟧ (ν C ∞) →⋆ ν C ∞
ν-in C =
  map C {A = ν C ∞} (λ x → record { force = λ { {j = _} → x } })

mutual

  -- The greatest fixpoint is greater than or equal to every
  -- post-fixpoint.

  unfold :
    ∀ {ℓ} {I : Set ℓ} (C : Container I I) {X : I → Set ℓ} →
    (X →⋆ ⟦ C ⟧ X) →
    ∀ {i} → X →⋆ ν C i
  unfold C f x = map C (unfold′ C f) (f x)

  unfold′ :
    ∀ {ℓ} {I : Set ℓ} (C : Container I I) {X : I → Set ℓ} →
    (X →⋆ ⟦ C ⟧ X) →
    ∀ {i} → X →⋆ ν′ C i
  force (unfold′ C f x) = unfold C f x

------------------------------------------------------------------------
-- Bisimilarity

mutual

  -- Bisimilarity for ν/ν′.
  --
  -- TODO: Define using a container?

  ν-bisimilar :
    ∀ {ℓ} {I : Set ℓ} {C : Container I I} {o} →
    Size → ν C ∞ o → ν C ∞ o → Set ℓ
  ν-bisimilar {C = C} i (s₁ , f₁) (s₂ , f₂) =
    ∃ λ (eq : s₁ ≡ s₂) →
    ∀ {o} (p : Container.Position C s₁ o) →
    ν′-bisimilar i
      (f₁ p)
      (f₂ (subst (λ s → Container.Position C s o) eq p))

  record ν′-bisimilar
           {ℓ} {I : Set ℓ} {C : Container I I} {o}
           (i : Size) (x y : ν′ C ∞ o) : Set ℓ where
    coinductive
    field
      force : {j : Size< i} → ν-bisimilar j (force x) (force y)

open ν′-bisimilar public

mutual

  -- Bisimilarity is reflexive.

  reflexive-ν :
    ∀ {ℓ} {I : Set ℓ} {C : Container I I} {o} {x : ν C ∞ o} {i} →
    ν-bisimilar i x x
  reflexive-ν = refl , λ _ → reflexive-ν′

  reflexive-ν′ :
    ∀ {ℓ} {I : Set ℓ} {C : Container I I} {o} {x : ν′ C ∞ o} {i} →
    ν′-bisimilar i x x
  force reflexive-ν′ = reflexive-ν

mutual

  -- Bisimilarity is symmetric.

  symmetric-ν :
    ∀ {ℓ} {I : Set ℓ} {C : Container I I} {o} {x y : ν C ∞ o} {i} →
    ν-bisimilar i x y → ν-bisimilar i y x
  symmetric-ν (refl , bisim) = refl , symmetric-ν′ ∘ bisim

  symmetric-ν′ :
    ∀ {ℓ} {I : Set ℓ} {C : Container I I} {o} {x y : ν′ C ∞ o} {i} →
    ν′-bisimilar i x y → ν′-bisimilar i y x
  force (symmetric-ν′ bisim) = symmetric-ν (force bisim)

mutual

  -- Bisimilarity is transitive.

  transitive-ν :
    ∀ {ℓ} {I : Set ℓ} {C : Container I I} {o} {x y z : ν C ∞ o} {i} →
    ν-bisimilar i x y → ν-bisimilar i y z → ν-bisimilar i x z
  transitive-ν (refl , bisim₁) (refl , bisim₂) =
    refl , λ p → transitive-ν′ (bisim₁ p) (bisim₂ p)

  transitive-ν′ :
    ∀ {ℓ} {I : Set ℓ} {C : Container I I} {o} {x y z : ν′ C ∞ o} {i} →
    ν′-bisimilar i x y → ν′-bisimilar i y z → ν′-bisimilar i x z
  force (transitive-ν′ {z = z} bisim₁ bisim₂) =
    transitive-ν {z = force z} (force bisim₁) (force bisim₂)

-- Extensionality for ν′ C: bisimilarity implies equality.
--
-- TODO: Is this a consistent assumption?

ν′-extensionality : ∀ {ℓ} {I : Set ℓ} → Container I I → Set ℓ
ν′-extensionality C =
  ∀ {o} {x y : ν′ C ∞ o} → ν′-bisimilar ∞ x y → x ≡ y

-- The formulation of extensionality given above for ν′ can be used to
-- derive a form of extensionality for ν.

ν-extensionality :
  ∀ {ℓ} {I : Set ℓ} {C : Container I I} →
  ν′-extensionality C →
  ∀ {o} {x y : ν C ∞ o} → ν-bisimilar ∞ x y → x ≡ y
ν-extensionality
  {C = C} ν′-ext {x = x@(s , f₁)} {y = y@(.s , f₂)} (refl , bisim) =

                                                             $⟨ (λ _ → bisim) ⟩
  (∀ o (p : Position C s o) → ν′-bisimilar ∞ (f₁ p) (f₂ p))  ↝⟨ (ν′-ext ∘_) ∘_ ⟩
  (∀ o (p : Position C s o) → f₁ p ≡ f₂ p)                   ↝⟨ implicit-extensionality ext ∘ (ext ∘_) ⟩
  (λ {_} → f₁) ≡ f₂                                          ↝⟨ cong (s ,_) ⟩□
  x ≡ y                                                      □

  where
  open Container

------------------------------------------------------------------------
-- More properties related to ν and ν′

-- The greatest fixpoint is a fixpoint in a different sense
-- (assuming extensionality and univalence).

ν-fixpoint :
  ∀ {ℓ} →
  Univalence ℓ →
  {I : Set ℓ} (C : Container I I) →
  ν′-extensionality C →
  ν C ∞ ≡ ⟦ C ⟧ (ν C ∞)
ν-fixpoint univ C ν′-ext =
  ν C ∞           ≡⟨⟩
  ⟦ C ⟧ (ν′ C ∞)  ≡⟨ cong ⟦ C ⟧ (ext λ _ → ≃⇒≡ univ (Eq.↔⇒≃ ν′↔ν)) ⟩
  ⟦ C ⟧ (ν C ∞)   ∎
  where
  ν′↔ν : ∀ {o} → ν′ C ∞ o ↔ ν C ∞ o
  ν′↔ν = record
    { surjection = record
      { logical-equivalence = record
        { to   = λ x → force x
        ; from = λ x → record { force = x }
        }
      ; right-inverse-of = λ _ → refl
      }
    ; left-inverse-of = λ x → ν′-ext (record { force = reflexive-ν })
    }

-- The unfold and unfold′ functions make certain diagrams commute.

unfold′-commute :
  ∀ {ℓ} {I : Set ℓ} (C : Container I I) {X : I → Set ℓ}
  (f : X →⋆ ⟦ C ⟧ X) →
  ∀ {i o} (x : X o) →
  ν′-bisimilar i
    (unfold′ C f x)
    (record { force = map C (unfold′ C f {i = ∞}) (f x) })
force (unfold′-commute C f x) = reflexive-ν

unfold-commute :
  ∀ {ℓ} {I : Set ℓ} (C : Container I I) {X : I → Set ℓ}
  (f : X →⋆ ⟦ C ⟧ X) →
  ∀ {i o} (x : X o) →
  ν-bisimilar i
    (unfold C f x)
    (ν-in C (map C (unfold C f) (f x)))
unfold-commute C f x = refl , unfold′-commute C f ∘ proj₂ (f x)

mutual

  -- Uniqueness properties for unfold and unfold′.

  unfold-unique :
    ∀ {ℓ} {I : Set ℓ} (C : Container I I) {X : I → Set ℓ}
    (f : X →⋆ ⟦ C ⟧ X) (u : X →⋆ ν C ∞) {i} →
    (∀ {o} (x : X o) →
     ν-bisimilar i (u x) (ν-in C (map C u (f x)))) →
    ∀ {o} (x : X o) → ν-bisimilar i (u x) (unfold C f x)
  unfold-unique C f u bisim x with bisim x
  ... | eq , bisim′ = eq , λ p →
    transitive-ν′ (bisim′ p)
                  (unfold′-unique C f u bisim _)

  unfold′-unique :
    ∀ {ℓ} {I : Set ℓ} (C : Container I I) {X : I → Set ℓ}
    (f : X →⋆ ⟦ C ⟧ X) (u : X →⋆ ν C ∞) {i} →
    (∀ {o} (x : X o) →
     ν-bisimilar i (u x) (ν-in C (map C u (f x)))) →
    ∀ {o} (x : X o) →
    ν′-bisimilar i (record { force = u x }) (unfold′ C f x)
  force (unfold′-unique C f u bisim x) = unfold-unique C f u bisim x
