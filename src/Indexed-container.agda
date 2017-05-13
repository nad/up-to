------------------------------------------------------------------------
-- Indexed containers
------------------------------------------------------------------------

-- Some parts are based on "Indexed containers" by Altenkirch, Ghani,
-- Hancock, McBride and Morris (JFP, 2015).

{-# OPTIONS --without-K #-}

module Indexed-container where

open import Equality.Propositional hiding (Extensionality)
open import Interval using (ext)
open import Logical-equivalence using (_⇔_)
open import Prelude

open import Bijection equality-with-J as Bijection using (_↔_)
import Equivalence equality-with-J as Eq
open import Function-universe equality-with-J as F hiding (id; _∘_)
open import H-level.Closure equality-with-J
open import Surjection equality-with-J using (_↠_)
open import Univalence-axiom equality-with-J

open import Relation

------------------------------------------------------------------------
-- Containers

-- Singly indexed containers.

record Container₁ {ℓ} (I : Set ℓ) : Set (lsuc ℓ) where
  constructor _◁₁_
  field
    Shape    : Set ℓ
    Position : Shape → Rel ℓ I

-- Doubly indexed containers.

Container : ∀ {ℓ} → Set ℓ → Set ℓ → Set (lsuc ℓ)
Container I O = O → Container₁ I

-- A "constructor".

_◁_ : ∀ {ℓ} {I O : Set ℓ} →
      (S : Rel ℓ O) → (∀ {o} → S o → Rel ℓ I) → Container I O
(S ◁ P) o = S o ◁₁ P

-- Some "projections".

module Container {ℓ} {I O : Set ℓ} (C : Container I O) where

  Shape : Rel ℓ O
  Shape = Container₁.Shape ∘ C

  Position : ∀ {o} → Shape o → Rel ℓ I
  Position = Container₁.Position (C _)

-- Interpretations of containers.

⟦_⟧₁ : ∀ {ℓ₁ ℓ₂} {I : Set ℓ₁} →
       Container₁ I → Rel ℓ₂ I → Set (ℓ₁ ⊔ ℓ₂)
⟦ S ◁₁ P ⟧₁ Q = ∃ λ (s : S) → P s ⊆ Q

⟦_⟧ : ∀ {ℓ₁ ℓ₂} {I O : Set ℓ₁} →
      Container I O → Rel ℓ₂ I → Rel (ℓ₁ ⊔ ℓ₂) O
⟦ C ⟧ Q o = ⟦ C o ⟧₁ Q

-- Map functions.

map₁ : ∀ {ℓ₁ ℓ₂ ℓ₃} {I : Set ℓ₁} {C : Container₁ I}
         {A : Rel ℓ₂ I} {B : Rel ℓ₃ I} →
       A ⊆ B → ⟦ C ⟧₁ A → ⟦ C ⟧₁ B
map₁ f = Σ-map id (λ g {_} → f ∘ g {_})

map : ∀ {ℓ₁ ℓ₂ ℓ₃} {I O : Set ℓ₁} (C : Container I O)
        {A : Rel ℓ₂ I} {B : Rel ℓ₃ I} →
      A ⊆ B → ⟦ C ⟧ A ⊆ ⟦ C ⟧ B
map _ f = map₁ f

------------------------------------------------------------------------
-- Least fixpoints

mutual

  -- The least fixpoint of an indexed "endocontainer", expressed using
  -- sized types.

  μ : ∀ {ℓ} {I : Set ℓ} → Container I I → Size → Rel ℓ I
  μ C i = ⟦ C ⟧ (μ′ C i)

  data μ′ {ℓ} {I : Set ℓ}
          (C : Container I I) (i : Size) (o : I) : Set ℓ where
    ⟨_⟩ : {j : Size< i} → μ C j o → μ′ C i o

-- An inverse of ⟨_⟩ (for fully defined values).

⟨_⟩⁻¹ :
  ∀ {ℓ} {I : Set ℓ} {C : Container I I} →
  μ′ C ∞ ⊆ μ C ∞
⟨ ⟨ x ⟩ ⟩⁻¹ = x

-- The least fixpoint is a post-fixpoint.

μ-out :
  ∀ {ℓ} {I : Set ℓ} {C : Container I I} →
  μ C ∞ ⊆ ⟦ C ⟧ (μ C ∞)
μ-out {C = C} = map C ⟨_⟩⁻¹

-- The greatest fixpoint is a pre-fixpoint.

μ-in :
  ∀ {ℓ} {I : Set ℓ} {C : Container I I} →
  ⟦ C ⟧ (μ C ∞) ⊆ μ C ∞
μ-in {C = C} = map C ⟨_⟩

mutual

  -- The least fixpoint is smaller than or equal to every
  -- pre-fixpoint.

  fold :
    ∀ {ℓ₁ ℓ₂} {I : Set ℓ₁} (C : Container I I) {X : Rel ℓ₂ I} →
    ⟦ C ⟧ X ⊆ X →
    ∀ {i} → μ C i ⊆ X
  fold C f x = f (map C (fold′ C f) x)

  fold′ :
    ∀ {ℓ₁ ℓ₂} {I : Set ℓ₁} (C : Container I I) {X : Rel ℓ₂ I} →
    ⟦ C ⟧ X ⊆ X →
    ∀ {i} → μ′ C i ⊆ X
  fold′ C f ⟨ x ⟩ = fold C f x

------------------------------------------------------------------------
-- Greatest fixpoints

mutual

  -- The greatest fixpoint of an indexed "endocontainer", expressed
  -- using sized types.

  ν : ∀ {ℓ} {I : Set ℓ} → Container I I → Size → Rel ℓ I
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
  ν C ∞ ⊆ ⟦ C ⟧ (ν C ∞)
ν-out {C = C} = map C (λ x → force x)

-- The greatest fixpoint is a pre-fixpoint.

ν-in :
  ∀ {ℓ} {I : Set ℓ} (C : Container I I) →
  ⟦ C ⟧ (ν C ∞) ⊆ ν C ∞
ν-in C =
  map C {A = ν C ∞} (λ x → record { force = λ { {j = _} → x } })

mutual

  -- The greatest fixpoint is greater than or equal to every
  -- post-fixpoint.

  unfold :
    ∀ {ℓ₁ ℓ₂} {I : Set ℓ₁} (C : Container I I) {X : Rel ℓ₂ I} →
    X ⊆ ⟦ C ⟧ X →
    ∀ {i} → X ⊆ ν C i
  unfold C f x = map C (unfold′ C f) (f x)

  unfold′ :
    ∀ {ℓ₁ ℓ₂} {I : Set ℓ₁} (C : Container I I) {X : Rel ℓ₂ I} →
    X ⊆ ⟦ C ⟧ X →
    ∀ {i} → X ⊆ ν′ C i
  force (unfold′ C f x) = unfold C f x

------------------------------------------------------------------------
-- Bisimilarity

-- A container corresponding to bisimilarity for a given container.

Bisimilarity :
  ∀ {ℓ} {I : Set ℓ} {C : Container I I} →
  let P = ∃ λ o → ν C ∞ o × ν C ∞ o in
  Container P P
Bisimilarity {C = C} =
  (λ { (_ , (s₁ , _) , (s₂ , _)) → s₁ ≡ s₂ })
    ◁
  (λ { {o = _ , (s₁ , f₁) , (s₂ , f₂)} eq (o , x₁ , x₂) →
       ∃ λ (p : Container.Position C s₁ o) →
       x₁ ≡ force (f₁ p)
         ×
       x₂ ≡ force (f₂ (subst (λ s → Container.Position C s o) eq p)) })

-- Bisimilarity for ν.

ν-bisimilar :
  ∀ {ℓ} {I : Set ℓ} {C : Container I I} {o} →
  Size → Rel₂ ℓ (ν C ∞ o)
ν-bisimilar i p = ν Bisimilarity i (_ , p)

ν′-bisimilar :
  ∀ {ℓ} {I : Set ℓ} {C : Container I I} {o} →
  Size → Rel₂ ℓ (ν′ C ∞ o)
ν′-bisimilar i (x , y) = ν′ Bisimilarity i (_ , force x , force y)

-- Lifts a family of binary relations from X to ⟦ C ⟧ X.

⟦_⟧₂ :
  ∀ {ℓ x} {I O : Set ℓ} {X : Rel x I} (C : Container I O) →
  (∀ {i} → Rel₂ ℓ (X i)) →
  ∀ {o} → Rel₂ ℓ (⟦ C ⟧ X o)
⟦ C ⟧₂ R ((s , f) , (t , g)) =
  ∃ λ (eq : s ≡ t) →
  ∀ {o} (p : Position C s o) →
  R (f p , g (subst (λ s → Position C s o) eq p))
  where
  open Container

-- An alternative characterisation of bisimilarity.

ν-bisimilar↔ :
  ∀ {ℓ} {I : Set ℓ} {C : Container I I} {o i} (x y : ν C ∞ o) →
  ν-bisimilar i (x , y) ↔ ⟦ C ⟧₂ (ν′-bisimilar i) (x , y)
ν-bisimilar↔ {C = C} {i = i} (s₁ , f₁) (s₂ , f₂) =

  ν-bisimilar i ((s₁ , f₁) , (s₂ , f₂))                             ↔⟨⟩

  (∃ λ (eq : s₁ ≡ s₂) →
   ∀ {o} →
   (∃ λ (p : Position C s₁ (proj₁ o)) →
      proj₁ (proj₂ o) ≡ force (f₁ p) ×
      proj₂ (proj₂ o) ≡
        force (f₂ (subst (λ s → Position C s (proj₁ o)) eq p))) →
   ν′ Bisimilarity i o)                                             ↝⟨ ∃-cong lemma ⟩

  (∃ λ (eq : s₁ ≡ s₂) →
   ∀ {o} (p : Position C s₁ o) →
   ν′-bisimilar i (f₁ p , f₂ (subst (λ s → Position C s o) eq p)))  ↔⟨⟩

  ⟦ C ⟧₂ (ν′-bisimilar i) ((s₁ , f₁) , (s₂ , f₂))                   □

  where
  open Container

  lemma = λ eq →

    (∀ {o} →
     (∃ λ (p : Position C s₁ (proj₁ o)) →
      proj₁ (proj₂ o) ≡ force (f₁ p) ×
      proj₂ (proj₂ o) ≡
        force (f₂ (subst (λ s → Position C s (proj₁ o)) eq p))) →
     ν′ Bisimilarity i o)                                                 ↝⟨ Bijection.implicit-Π↔Π ⟩

    (∀ o →
     (∃ λ (p : Position C s₁ (proj₁ o)) →
      proj₁ (proj₂ o) ≡ force (f₁ p) ×
      proj₂ (proj₂ o) ≡
        force (f₂ (subst (λ s → Position C s (proj₁ o)) eq p))) →
     ν′ Bisimilarity i o)                                                 ↝⟨ (∀-cong ext λ _ → currying) ⟩

    (∀ o (p : Position C s₁ (proj₁ o)) →
     proj₁ (proj₂ o) ≡ force (f₁ p) ×
     proj₂ (proj₂ o) ≡
       force (f₂ (subst (λ s → Position C s (proj₁ o)) eq p)) →
     ν′ Bisimilarity i o)                                                 ↝⟨ (∀-cong ext λ _ → ∀-cong ext λ _ → currying) ⟩

    (∀ o (p : Position C s₁ (proj₁ o)) →
     proj₁ (proj₂ o) ≡ force (f₁ p) →
     proj₂ (proj₂ o) ≡
       force (f₂ (subst (λ s → Position C s (proj₁ o)) eq p)) →
     ν′ Bisimilarity i o)                                                 ↝⟨ currying ⟩

    (∀ o xy (p : Position C s₁ o) →
     proj₁ xy ≡ force (f₁ p) →
     proj₂ xy ≡ force (f₂ (subst (λ s → Position C s o) eq p)) →
     ν′ Bisimilarity i (o , xy))                                          ↝⟨ (∀-cong ext λ _ → Π-comm) ⟩

    (∀ o (p : Position C s₁ o) xy →
     proj₁ xy ≡ force (f₁ p) →
     proj₂ xy ≡ force (f₂ (subst (λ s → Position C s o) eq p)) →
     ν′ Bisimilarity i (o , xy))                                          ↝⟨ (∀-cong ext λ _ → ∀-cong ext λ _ → currying) ⟩

    (∀ o (p : Position C s₁ o) x y →
     x ≡ force (f₁ p) →
     y ≡ force (f₂ (subst (λ s → Position C s o) eq p)) →
     ν′ Bisimilarity i (o , x , y))                                       ↝⟨ (∀-cong ext λ _ → ∀-cong ext λ _ → ∀-cong ext λ _ → Π-comm) ⟩

    (∀ o (p : Position C s₁ o) →
     ∀ x → x ≡ force (f₁ p) →
     ∀ y → y ≡ force (f₂ (subst (λ s → Position C s o) eq p)) →
     ν′ Bisimilarity i (o , x , y))                                       ↝⟨ (∀-cong ext λ _ → ∀-cong ext λ _ → inverse currying) ⟩

    (∀ o (p : Position C s₁ o) →
     (x : ∃ λ x → x ≡ force (f₁ p)) →
     ∀ y → y ≡ force (f₂ (subst (λ s → Position C s o) eq p)) →
     ν′ Bisimilarity i (o , proj₁ x , y))                                 ↝⟨ (∀-cong ext λ _ → ∀-cong ext λ _ → drop-⊤-left-Π ext (
                                                                              _⇔_.to contractible⇔↔⊤ $ singleton-contractible _)) ⟩
    (∀ o (p : Position C s₁ o) →
     ∀ y → y ≡ force (f₂ (subst (λ s → Position C s o) eq p)) →
     ν′ Bisimilarity i (o , force (f₁ p) , y))                            ↝⟨ (∀-cong ext λ _ → ∀-cong ext λ _ → inverse currying) ⟩

    (∀ o (p : Position C s₁ o) →
     (y : ∃ λ y → y ≡ force (f₂ (subst (λ s → Position C s o) eq p))) →
     ν′ Bisimilarity i (o , force (f₁ p) , proj₁ y))                      ↝⟨ (∀-cong ext λ _ → ∀-cong ext λ _ → drop-⊤-left-Π ext (
                                                                              _⇔_.to contractible⇔↔⊤ $ singleton-contractible _)) ⟩
    (∀ o (p : Position C s₁ o) →
     ν′ Bisimilarity i
       (o , force (f₁ p)
          , force (f₂ (subst (λ s → Position C s o) eq p))))              ↝⟨ inverse $ Bijection.implicit-Π↔Π ⟩

    (∀ {o} (p : Position C s₁ o) →
     ν′ Bisimilarity i
       (o , force (f₁ p)
          , force (f₂ (subst (λ s → Position C s o) eq p))))              ↔⟨⟩

    (∀ {o} (p : Position C s₁ o) →
     ν′-bisimilar i (f₁ p , f₂ (subst (λ s → Position C s o) eq p)))      □

module Bisimilarity
         {ℓ} {I : Set ℓ} {C : Container I I}
         {o i} (x y : ν C ∞ o)
         where

  -- A "constructor".

  ⟨_,_,_,_⟩ :
    (eq : proj₁ x ≡ proj₁ y) →
    (∀ {o} (p : Container.Position C (proj₁ x) o) →
     ν′-bisimilar i
       ( proj₂ x p
       , proj₂ y (subst (λ s → Container.Position C s o) eq p)
       )) →
    ν-bisimilar i (x , y)
  ⟨_,_,_,_⟩ = curry $ _↔_.from (ν-bisimilar↔ x y)

  -- A "projection".

  split : ν-bisimilar i (x , y) → ⟦ C ⟧₂ (ν′-bisimilar i) (x , y)
  split = _↔_.to (ν-bisimilar↔ x y)

mutual

  -- Bisimilarity is reflexive.

  reflexive-ν :
    ∀ {ℓ} {I : Set ℓ} {C : Container I I} {o} (x : ν C ∞ o) {i} →
    ν-bisimilar i (x , x)
  reflexive-ν x =
    Bisimilarity.⟨ x , x , refl , (λ p → reflexive-ν′ (proj₂ x p)) ⟩

  reflexive-ν′ :
    ∀ {ℓ} {I : Set ℓ} {C : Container I I} {o} (x : ν′ C ∞ o) {i} →
    ν′-bisimilar i (x , x)
  force (reflexive-ν′ x) = reflexive-ν (force x)

mutual

  -- Bisimilarity is symmetric.

  symmetric-ν :
    ∀ {ℓ} {I : Set ℓ} {C : Container I I} {o} (x y : ν C ∞ o) {i} →
    ν-bisimilar i (x , y) → ν-bisimilar i (y , x)
  symmetric-ν x y bisim with Bisimilarity.split x y bisim
  ... | refl , bisim′ =
    Bisimilarity.⟨ y
                 , x
                 , refl
                 , (λ p → symmetric-ν′ (proj₂ x p) (proj₂ y p)
                                       (bisim′ p))
                 ⟩

  symmetric-ν′ :
    ∀ {ℓ} {I : Set ℓ} {C : Container I I} {o} (x y : ν′ C ∞ o) {i} →
    ν′-bisimilar i (x , y) → ν′-bisimilar i (y , x)
  force (symmetric-ν′ x y bisim) =
    symmetric-ν (force x) (force y) (force bisim)

mutual

  -- Bisimilarity is transitive.

  transitive-ν :
    ∀ {ℓ} {I : Set ℓ} {C : Container I I} {o} (x y z : ν C ∞ o) {i} →
    ν-bisimilar i (x , y) → ν-bisimilar i (y , z) →
    ν-bisimilar i (x , z)
  transitive-ν x y z bisim₁ bisim₂ with Bisimilarity.split x y bisim₁
                                      | Bisimilarity.split y z bisim₂
  ... | refl , bisim₁′ | refl , bisim₂′ =
    Bisimilarity.⟨ x
                 , z
                 , refl
                 , (λ p → transitive-ν′
                            (proj₂ x p) (proj₂ y p) (proj₂ z p)
                            (bisim₁′ p) (bisim₂′ p))
                 ⟩

  transitive-ν′ :
    ∀ {ℓ} {I : Set ℓ} {C : Container I I} {o} (x y z : ν′ C ∞ o) {i} →
    ν′-bisimilar i (x , y) → ν′-bisimilar i (y , z) →
    ν′-bisimilar i (x , z)
  force (transitive-ν′ x y z bisim₁ bisim₂) =
    transitive-ν (force x) (force y) (force z)
                 (force bisim₁) (force bisim₂)

-- Extensionality for ν′ C: bisimilarity implies equality.
--
-- TODO: Is this a consistent assumption?

ν′-extensionality : ∀ {ℓ} {I : Set ℓ} → Container I I → Set ℓ
ν′-extensionality C =
  ∀ {o} {x y : ν′ C ∞ o} → ν′-bisimilar ∞ (x , y) → x ≡ y

-- The formulation of extensionality given above for ν′ can be used to
-- derive a form of extensionality for ν.

ν-extensionality :
  ∀ {ℓ} {I : Set ℓ} {C : Container I I} →
  ν′-extensionality C →
  ∀ {o} {x y : ν C ∞ o} → ν-bisimilar ∞ (x , y) → x ≡ y
ν-extensionality
  {C = C} ν′-ext {x = x@(s , f₁)} {y = y@(.s , f₂)} bisim@(refl , _) =

                                                             $⟨ (λ _ → proj₂ $ Bisimilarity.split x y bisim) ⟩
  (∀ o (p : Position C s o) → ν′-bisimilar ∞ (f₁ p , f₂ p))  ↝⟨ (ν′-ext ∘_) ∘_ ⟩
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
    ; left-inverse-of = λ x →
        ν′-ext (record { force = reflexive-ν (force x) })
    }

-- The unfold and unfold′ functions make certain diagrams commute.

unfold′-commute :
  ∀ {ℓ₁ ℓ₂} {I : Set ℓ₁} (C : Container I I) {X : Rel ℓ₂ I}
  (f : X ⊆ ⟦ C ⟧ X) →
  ∀ {i o} (x : X o) →
  ν′-bisimilar i
    ( unfold′ C f x
    , record { force = map C (unfold′ C f {i = ∞}) (f x) }
    )
force (unfold′-commute C f x) = reflexive-ν (unfold C f x)

unfold-commute :
  ∀ {ℓ₁ ℓ₂} {I : Set ℓ₁} (C : Container I I) {X : Rel ℓ₂ I}
  (f : X ⊆ ⟦ C ⟧ X) →
  ∀ {i o} (x : X o) →
  ν-bisimilar i
    ( unfold C f x
    , ν-in C (map C (unfold C f) (f x))
    )
unfold-commute C f x =
  Bisimilarity.⟨ unfold C f x
               , ν-in C (map C (unfold C f) (f x))
               , refl
               , unfold′-commute C f ∘ proj₂ (f x)
               ⟩

mutual

  -- Uniqueness properties for unfold and unfold′.

  unfold-unique :
    ∀ {ℓ₁ ℓ₂} {I : Set ℓ₁} (C : Container I I) {X : Rel ℓ₂ I}
    (f : X ⊆ ⟦ C ⟧ X) (u : X ⊆ ν C ∞) {i} →
    (∀ {o} (x : X o) →
     ν-bisimilar i (u x , ν-in C (map C u (f x)))) →
    ∀ {o} (x : X o) → ν-bisimilar i (u x , unfold C f x)
  unfold-unique C f u bisim x
    with Bisimilarity.split (u x) (ν-in C (map C u (f x))) (bisim x)
  ... | eq , bisim′ =
    Bisimilarity.⟨ u x
                 , unfold C f x
                 , eq
                 , (λ p →
                      let p′ = subst (λ s → Container.Position C s _)
                                     eq p in
                      transitive-ν′
                        (proj₂ (u x) p)
                        (proj₂ (ν-in C (map C u (f x))) p′)
                        (proj₂ (unfold C f x) p′)
                        (bisim′ p)
                        (unfold′-unique C f u bisim _))
                 ⟩

  unfold′-unique :
    ∀ {ℓ₁ ℓ₂} {I : Set ℓ₁} (C : Container I I) {X : Rel ℓ₂ I}
    (f : X ⊆ ⟦ C ⟧ X) (u : X ⊆ ν C ∞) {i} →
    (∀ {o} (x : X o) →
     ν-bisimilar i (u x , ν-in C (map C u (f x)))) →
    ∀ {o} (x : X o) →
    ν′-bisimilar i (record { force = u x } , unfold′ C f x)
  force (unfold′-unique C f u bisim x) = unfold-unique C f u bisim x

------------------------------------------------------------------------
-- An alternative definition of greatest fixpoints

-- The greatest fixpoint of an indexed "endocontainer" (parametrised
-- by a universe level).

gfp : ∀ {ℓ₁} ℓ₂ {I : Set ℓ₁} → Container I I → Rel (lsuc (ℓ₁ ⊔ ℓ₂)) I
gfp {ℓ₁} ℓ₂ {I} C i = ∃ λ (R : Rel (ℓ₁ ⊔ ℓ₂) I) → R ⊆ ⟦ C ⟧ R × R i

-- The greatest fixpoint is greater than or equal to every
-- sufficiently small post-fixpoint.

gfp-unfold :
  ∀ {ℓ₁ ℓ₂} ℓ₃ {I : Set ℓ₁} {C : Container I I} {X : Rel ℓ₂ I} →
  X ⊆ ⟦ C ⟧ X →
  X ⊆ gfp (ℓ₂ ⊔ ℓ₃) C
gfp-unfold {ℓ₁} ℓ₃ {C = C} {X} f x =
  ↑ (ℓ₁ ⊔ ℓ₃) ∘ X , map C lift ∘ f ∘ lower , lift x

-- The greatest fixpoint is a post-fixpoint.

gfp-out : ∀ {ℓ₁} ℓ₂ {I : Set ℓ₁} {C : Container I I} →
          gfp ℓ₂ C ⊆ ⟦ C ⟧ (gfp ℓ₂ C)
gfp-out ℓ₂ {C = C} (R , R⊆CR , Ri) =
  map C (λ Ri → R , (λ {_} → R⊆CR) , Ri) (R⊆CR Ri)

  -- It is possible to use gfp-unfold ℓ₂ R⊆CR as the second argument
  -- to map above. However, the extra lifting would break the proof
  -- gfp⊆ν∘ν⊆gfp given below.

-- The first definition of greatest fixpoints is contained in the
-- second one.

ν⊆gfp : ∀ {ℓ₁} ℓ₂ {I : Set ℓ₁} {C : Container I I} →
        ν C ∞ ⊆ gfp ℓ₂ C
ν⊆gfp ℓ₂ = gfp-unfold ℓ₂ ν-out

-- The second definition of greatest fixpoints is contained in the first one.

gfp⊆ν : ∀ {ℓ₁} ℓ₂ {I : Set ℓ₁} {C : Container I I} {i} →
        gfp ℓ₂ C ⊆ ν C i
gfp⊆ν ℓ₂ = unfold _ (gfp-out ℓ₂)

-- Thus the two definitions of greatest fixpoints are pointwise
-- logically equivalent.

gfp⇔ν : ∀ {ℓ₁} ℓ₂ {I : Set ℓ₁} {C : Container I I} {i} →
        gfp ℓ₂ C i ⇔ ν C ∞ i
gfp⇔ν ℓ₂ = record
  { to   = gfp⊆ν ℓ₂
  ; from = ν⊆gfp ℓ₂
  }

-- The function gfp⊆ν is a left inverse of ν⊆gfp.

gfp⊆ν∘ν⊆gfp :
  ∀ {ℓ₁} ℓ₂ {I : Set ℓ₁} {C : Container I I} {i} (x : ν C ∞ i) {i} →
  ν-bisimilar i (gfp⊆ν ℓ₂ (ν⊆gfp ℓ₂ x) , x)
gfp⊆ν∘ν⊆gfp {ℓ₁} ℓ₂ {I} {C} x =
  _↔_.from (ν-bisimilar↔ (gfp⊆ν ℓ₂ (ν⊆gfp ℓ₂ x)) x)
    ( refl
    , λ p → gfp⊆ν∘ν⊆gfp′ (proj₂ x p)
    )
  where
  gfp⊆ν∘ν⊆gfp′ :
    ∀ {i} (x : ν′ C ∞ i) {i} →
    ν′-bisimilar i (unfold′ _ (gfp-out ℓ₂) (ν⊆gfp ℓ₂ (force x)) , x)
  force (gfp⊆ν∘ν⊆gfp′ x) = gfp⊆ν∘ν⊆gfp ℓ₂ (force x)

-- There is a split surjection from the second definition of greatest
-- fixpoints to the first one (assuming extensionality).

gfp↠ν :
  ∀ {ℓ₁} ℓ₂ {I : Set ℓ₁} {C : Container I I} →
  ν′-extensionality C →
  ∀ {i} → gfp ℓ₂ C i ↠ ν C ∞ i
gfp↠ν ℓ₂ ext = record
  { logical-equivalence = gfp⇔ν ℓ₂
  ; right-inverse-of    = λ x →
      ν-extensionality ext (gfp⊆ν∘ν⊆gfp ℓ₂ x)
  }

-- The larger versions of gfp are logically equivalent to the smallest
-- one.

larger⇔smallest :
  ∀ {ℓ₁} ℓ₂ {I : Set ℓ₁} {C : Container I I} {i} →
  gfp ℓ₂ C i ⇔ gfp lzero C i
larger⇔smallest {ℓ₁} ℓ₂ {C = C} {i} =
  gfp ℓ₂ C i     ↝⟨ gfp⇔ν ℓ₂ ⟩
  ν C ∞ i        ↝⟨ inverse $ gfp⇔ν lzero ⟩□
  gfp lzero C i  □

------------------------------------------------------------------------
-- Container combinators

-- A reindexing combinator.

reindex₂ : ∀ {ℓ} {I O₁ O₂ : Set ℓ} →
           (O₂ → O₁) → Container I O₁ → Container I O₂
reindex₂ f C = C ∘ f

⟦reindex₂⟧ : ∀ {ℓ x} {I O₁ O₂ : Set ℓ} {f : O₂ → O₁}
             (C : Container I O₁) {X : Rel x I} {o} →
             ⟦ reindex₂ f C ⟧ X o ↔ ⟦ C ⟧ X (f o)
⟦reindex₂⟧ C = Bijection.id

-- An unfolding lemma for ⟦ reindex₂ f C ⟧₂.

⟦reindex₂⟧₂↔ :
  ∀ {ℓ x} {I O : Set ℓ} {X : Rel x I}
  (C : Container I O) (f : I → O) (R : ∀ {i} → Rel₂ ℓ (X i)) {i}
  (x y : ⟦ reindex₂ f C ⟧ X i) →

  ⟦ reindex₂ f C ⟧₂ R (x , y) ↔ ⟦ C ⟧₂ R (x , y)

⟦reindex₂⟧₂↔ C f R x@(s , g) y@(t , h) =

  ⟦ reindex₂ f C ⟧₂ R (x , y)                              ↔⟨⟩

  (∃ λ (eq : s ≡ t) →
   ∀ {o} (p : Position (C ∘ f) s o) →
   R (g p , h (subst (λ s → Position (C ∘ f) s o) eq p)))  ↔⟨⟩

  (∃ λ (eq : s ≡ t) →
   ∀ {o} (p : Position C s o) →
   R (g p , h (subst (λ s → Position C s o) eq p)))        ↔⟨⟩

  ⟦ C ⟧₂ R (x , y)                                         □

  where
  open Container

-- Another reindexing combinator.

reindex₁ : ∀ {ℓ} {I₁ I₂ O : Set ℓ} →
           (I₁ → I₂) → Container I₁ O → Container I₂ O
reindex₁ f C =
  Shape C
    ◁
  (λ s i → ∃ λ i′ → f i′ ≡ i × Position C s i′)
  where
  open Container

⟦reindex₁⟧ : ∀ {ℓ x} {I₁ I₂ O : Set ℓ} {f : I₁ → I₂}
             (C : Container I₁ O) {X : Rel x I₂} {o} →
             ⟦ reindex₁ f C ⟧ X o ↔ ⟦ C ⟧ (X ∘ f) o
⟦reindex₁⟧ {f = f} C {X} {o} =
  ⟦ reindex₁ f C ⟧ X o                                 ↝⟨ (∃-cong λ _ → Bijection.implicit-Π↔Π) ⟩

  (∃ λ (s : Shape C o) →
   ∀ i → (∃ λ i′ → f i′ ≡ i × Position C s i′) → X i)  ↝⟨ (∃-cong λ _ → ∀-cong ext λ _ → currying) ⟩

  (∃ λ (s : Shape C o) →
   ∀ i i′ → f i′ ≡ i × Position C s i′ → X i)          ↝⟨ (∃-cong λ _ → ∀-cong ext λ _ → ∀-cong ext λ _ → currying) ⟩

  (∃ λ (s : Shape C o) →
   ∀ i i′ → f i′ ≡ i → Position C s i′ → X i)          ↝⟨ (∃-cong λ _ → Π-comm) ⟩

  (∃ λ (s : Shape C o) →
   ∀ i i′ → f i ≡ i′ → Position C s i → X i′)          ↝⟨ (∃-cong λ _ → ∀-cong ext λ _ → inverse $ ∀-intro ext _) ⟩

  (∃ λ (s : Shape C o) →
   ∀ i → Position C s i → X (f i))                     ↝⟨ (∃-cong λ _ → inverse Bijection.implicit-Π↔Π) ⟩

  ⟦ C ⟧ (X ∘ f) o                                      □
  where
  open Container

-- An unfolding lemma for ⟦ reindex₁ f C ⟧₂.

⟦reindex₁⟧₂↔ :
  ∀ {ℓ x} {I O : Set ℓ} {X : Rel x O}
  (C : Container I O) (f : I → O) (R : ∀ {o} → Rel₂ ℓ (X o)) {o}
  (x y : ⟦ reindex₁ f C ⟧ X o) →

  ⟦ reindex₁ f C ⟧₂ R (x , y)

    ↔

  ⟦ C ⟧₂ R ( (proj₁ x , λ p → proj₂ x (_ , refl , p))
           , (proj₁ y , λ p → proj₂ y (_ , refl , p))
           )

⟦reindex₁⟧₂↔ C f R x@(s , g) y@(t , h) =

  ⟦ reindex₁ f C ⟧₂ R (x , y)                                             ↔⟨⟩

  (∃ λ (eq : s ≡ t) →
   ∀ {o} (p : ∃ λ o′ → f o′ ≡ o × Position C s o′) →
   R (g p , h (subst (λ s → ∃ λ o′ → f o′ ≡ o × Position C s o′) eq p)))  ↝⟨ (∃-cong λ eq → implicit-∀-cong ext $ ∀-cong ext λ _ →
                                                                              ≡⇒↝ _ $ cong (R ∘ (g _ ,_) ∘ h) $
                                                                              lemma eq) ⟩
  (∃ λ (eq : s ≡ t) →
   ∀ {o} (p : ∃ λ o′ → f o′ ≡ o × Position C s o′) →
   R ( g p
     , h ( proj₁ p
         , proj₁ (proj₂ p)
         , subst (λ s → Position C s (proj₁ p)) eq (proj₂ (proj₂ p))
         )
     ))                                                                   ↝⟨ (∃-cong λ _ → implicit-∀-cong ext $
                                                                              currying) ⟩
  (∃ λ (eq : s ≡ t) →
   ∀ {o} o′ (p : f o′ ≡ o × Position C s o′) →
   R ( g (o′ , p)
     , h (o′ , proj₁ p , subst (λ s → Position C s o′) eq (proj₂ p))
     ))                                                                   ↝⟨ (∃-cong λ _ → implicit-∀-cong ext $ ∀-cong ext λ _ →
                                                                              currying) ⟩
  (∃ λ (eq : s ≡ t) →
   ∀ {o} o′ (≡o : f o′ ≡ o) (p : Position C s o′) →
   R ( g (o′ , ≡o , p)
     , h (o′ , ≡o , subst (λ s → Position C s o′) eq p)
     ))                                                                   ↝⟨ (∃-cong λ _ →
                                                                              Bijection.implicit-Π↔Π) ⟩
  (∃ λ (eq : s ≡ t) →
   ∀ o o′ (≡o : f o′ ≡ o) (p : Position C s o′) →
   R ( g (o′ , ≡o , p)
     , h (o′ , ≡o , subst (λ s → Position C s o′) eq p)
     ))                                                                   ↝⟨ (∃-cong λ _ →
                                                                              Π-comm) ⟩
  (∃ λ (eq : s ≡ t) →
   ∀ o o′ (≡o′ : f o ≡ o′) (p : Position C s o) →
   R ( g (o , ≡o′ , p)
     , h (o , ≡o′ , subst (λ s → Position C s o) eq p)
     ))                                                                   ↝⟨ (∃-cong λ _ → ∀-cong ext λ _ → inverse $
                                                                              ∀-intro ext _) ⟩
  (∃ λ (eq : s ≡ t) →
   ∀ o (p : Position C s o) →
   R ( g (o , refl , p)
     , h (o , refl , subst (λ s → Position C s o) eq p)
     ))                                                                   ↝⟨ (∃-cong λ _ → inverse
                                                                              Bijection.implicit-Π↔Π) ⟩
  (∃ λ (eq : s ≡ t) →
   ∀ {o} (p : Position C s o) →
   R ( g (o , refl , p)
     , h (o , refl , subst (λ s → Position C s o) eq p)
     ))                                                                   ↔⟨⟩

  ⟦ C ⟧₂ R ((s , λ p → g (_ , refl , p)) , (t , λ p → h (_ , refl , p)))  □

  where
  open Container

  lemma = λ (eq : s ≡ t) {o} {p : ∃ λ o′ → f o′ ≡ o × Position C s o′} →

    subst (λ s → ∃ λ o′ → f o′ ≡ o × Position C s o′) eq p                ≡⟨ push-subst-pair′ {y≡z = eq} _ _ (subst-const eq) ⟩

    ( proj₁ p
    , subst (λ { (s , o′) → f o′ ≡ o × Position C s o′ })
            (Σ-≡,≡→≡ eq (subst-const eq)) (proj₂ p)
    )                                                                     ≡⟨⟩

    ( proj₁ p
    , subst (λ { (s , o′) → f o′ ≡ o × Position C s o′ })
            (Σ-≡,≡→≡ eq (trans (subst-const eq) refl)) (proj₂ p)
    )                                                                     ≡⟨ cong (λ eq → _ , subst (λ { (s , o′) → f o′ ≡ o × Position C s o′ })
                                                                                                    eq (proj₂ p)) $
                                                                             Σ-≡,≡→≡-subst-const eq refl ⟩
    ( proj₁ p
    , subst (λ { (s , o′) → f o′ ≡ o × Position C s o′ })
            (cong₂ _,_ eq refl) (proj₂ p)
    )                                                                     ≡⟨ cong (_ ,_) $
                                                                             push-subst-, {y≡z = cong₂ _,_ eq refl}
                                                                                          ((_≡ o) ∘ f ∘ proj₂) (uncurry (Position C)) ⟩
    ( proj₁ p
    , subst ((_≡ o) ∘ f ∘ proj₂)   (cong₂ _,_ eq refl) (proj₁ (proj₂ p))
    , subst (uncurry (Position C)) (cong₂ _,_ eq refl) (proj₂ (proj₂ p))
    )                                                                     ≡⟨ cong (λ eq′ → _ , eq′
                                                                                             , subst (uncurry (Position C)) (cong₂ _,_ eq refl) _) $
                                                                             subst-∘ ((_≡ o) ∘ f) proj₂ (cong₂ _,_ eq refl) ⟩
    ( proj₁ p
    , subst ((_≡ o) ∘ f)
            (cong proj₂ (cong₂ _,_ eq refl)) (proj₁ (proj₂ p))
    , subst (uncurry (Position C)) (cong (_, _) eq) (proj₂ (proj₂ p))
    )                                                                     ≡⟨ cong₂ (λ eq₁ eq₂ → _ , subst ((_≡ o) ∘ f) eq₁ _ , eq₂)
                                                                             (cong-proj₂-cong₂-, eq refl)
                                                                             (sym $ subst-∘ (uncurry (Position C)) (_, _) eq) ⟩
    ( proj₁ p
    , subst ((_≡ o) ∘ f) refl (proj₁ (proj₂ p))
    , subst (uncurry (Position C) ∘ (_, _)) eq (proj₂ (proj₂ p))
    )                                                                     ≡⟨⟩

    ( proj₁ p
    , proj₁ (proj₂ p)
    , subst (λ s → Position C s (proj₁ p)) eq (proj₂ (proj₂ p))
    )                                                                     ∎

-- A cartesian product combinator.
--
-- Similar to a construction in "Containers: Constructing strictly
-- positive types" by Abbott, Altenkirch and Ghani (see
-- Proposition 3.5).

infixr 2 _⊗_

_⊗_ : ∀ {ℓ} {I O : Set ℓ} →
      Container I O → Container I O → Container I O
C₁ ⊗ C₂ =
  (λ o → Shape C₁ o × Shape C₂ o)
    ◁
  (λ { (s₁ , s₂) i → Position C₁ s₁ i ⊎ Position C₂ s₂ i })
  where
  open Container

⟦⊗⟧ : ∀ {ℓ x} {I O : Set ℓ}
      (C₁ C₂ : Container I O) {X : Rel x I} {o} →
      ⟦ C₁ ⊗ C₂ ⟧ X o ↔ ⟦ C₁ ⟧ X o × ⟦ C₂ ⟧ X o
⟦⊗⟧ C₁ C₂ {X} {o} =
  ⟦ C₁ ⊗ C₂ ⟧ X o                                                  ↔⟨⟩

  (∃ λ (s : Shape C₁ o × Shape C₂ o) →
   (λ i → Position C₁ (proj₁ s) i ⊎ Position C₂ (proj₂ s) i) ⊆ X)  ↝⟨ inverse Σ-assoc ⟩

  (∃ λ (s₁ : Shape C₁ o) →
   ∃ λ (s₂ : Shape C₂ o) →
   (λ i → Position C₁ s₁ i ⊎ Position C₂ s₂ i) ⊆ X)                ↝⟨ (∃-cong λ _ → ∃-cong λ _ → implicit-∀-cong ext $ Π⊎↔Π×Π ext) ⟩

  (∃ λ (s₁ : Shape C₁ o) →
   ∃ λ (s₂ : Shape C₂ o) →
   ∀ {i} → (Position C₁ s₁ i → X i) × (Position C₂ s₂ i → X i))    ↝⟨ (∃-cong λ _ → ∃-cong λ _ → implicit-ΠΣ-comm) ⟩

  (∃ λ (s₁ : Shape C₁ o) →
   ∃ λ (s₂ : Shape C₂ o) →
   Position C₁ s₁ ⊆ X × Position C₂ s₂ ⊆ X)                        ↝⟨ (∃-cong λ _ → ∃-comm) ⟩

  (∃ λ (s₁ : Shape C₁ o) →
   Position C₁ s₁ ⊆ X
     ×
   ∃ λ (s₂ : Shape C₂ o) → Position C₂ s₂ ⊆ X)                     ↝⟨ Σ-assoc ⟩

  (∃ λ (s : Shape C₁ o) → Position C₁ s ⊆ X) ×
  (∃ λ (s : Shape C₂ o) → Position C₂ s ⊆ X)                       ↔⟨⟩

  ⟦ C₁ ⟧ X o × ⟦ C₂ ⟧ X o                                          □
  where
  open Container

-- An unfolding lemma for ⟦ C₁ ⊗ C₂ ⟧₂.

⟦⊗⟧₂↔ :
  ∀ {ℓ x} {I : Set ℓ} {X : Rel x I}
  (C₁ C₂ : Container I I) (R : ∀ {i} → Rel₂ ℓ (X i)) {i}
  (x y : ⟦ C₁ ⊗ C₂ ⟧ X i) →

  let (x₁ , x₂) , f = x
      (y₁ , y₂) , g = y
  in

  ⟦ C₁ ⊗ C₂ ⟧₂ R (x , y)

    ↔

  ⟦ C₁ ⟧₂ R ((x₁ , f ∘ inj₁) , (y₁ , g ∘ inj₁))
    ×
  ⟦ C₂ ⟧₂ R ((x₂ , f ∘ inj₂) , (y₂ , g ∘ inj₂))

⟦⊗⟧₂↔ C₁ C₂ R (x@(x₁ , x₂) , f) (y@(y₁ , y₂) , g) =

  ⟦ C₁ ⊗ C₂ ⟧₂ R ((x , f) , (y , g))                                      ↔⟨⟩

  (∃ λ (eq : x ≡ y) →
   ∀ {o} (p : Position (C₁ ⊗ C₂) x o) →
   R (f p , g (subst (λ s → Position (C₁ ⊗ C₂) s o) eq p)))               ↔⟨⟩

  (∃ λ (eq : x ≡ y) →
   ∀ {o} (p : Position C₁ x₁ o ⊎ Position C₂ x₂ o) →
   R ( f p
     , g (subst (λ { (s₁ , s₂) → Position C₁ s₁ o ⊎ Position C₂ s₂ o })
                eq p)
     ))                                                                   ↝⟨ inverse (Σ-cong ≡×≡↔≡ λ _ → F.id) ⟩

  (∃ λ (eq : x₁ ≡ y₁ × x₂ ≡ y₂) →
   ∀ {o} (p : Position C₁ x₁ o ⊎ Position C₂ x₂ o) →
   R ( f p
     , g (subst (λ { (s₁ , s₂) → Position C₁ s₁ o ⊎ Position C₂ s₂ o })
                (cong₂ _,_ (proj₁ eq) (proj₂ eq)) p)
     ))                                                                   ↝⟨ inverse Σ-assoc ⟩

  (∃ λ (eq₁ : x₁ ≡ y₁) →
   ∃ λ (eq₂ : x₂ ≡ y₂) →
   ∀ {o} (p : Position C₁ x₁ o ⊎ Position C₂ x₂ o) →
   R ( f p
     , g (subst (λ { (s₁ , s₂) → Position C₁ s₁ o ⊎ Position C₂ s₂ o })
                (cong₂ _,_ eq₁ eq₂) p)
     ))                                                                   ↝⟨ (∃-cong λ _ → ∃-cong λ _ → implicit-∀-cong ext $ Π⊎↔Π×Π ext) ⟩

  (∃ λ (eq₁ : x₁ ≡ y₁) →
   ∃ λ (eq₂ : x₂ ≡ y₂) →
   ∀ {o} →
   ((p : Position C₁ x₁ o) →
    R ( f (inj₁ p)
      , g (subst (λ { (s₁ , s₂) → Position C₁ s₁ o ⊎ Position C₂ s₂ o })
                 (cong₂ _,_ eq₁ eq₂) (inj₁ p))
      ))
     ×
   ((p : Position C₂ x₂ o) →
    R ( f (inj₂ p)
      , g (subst (λ { (s₁ , s₂) → Position C₁ s₁ o ⊎ Position C₂ s₂ o })
                 (cong₂ _,_ eq₁ eq₂) (inj₂ p))
      )))                                                                 ↝⟨ (∃-cong λ eq₁ → ∃-cong λ eq₂ → implicit-∀-cong ext $
                                                                              (∀-cong ext λ _ → ≡⇒↝ _ $ cong (R ∘ (f _ ,_)) $
                                                                               lemma₁ eq₁ eq₂)
                                                                                ×-cong
                                                                              (∀-cong ext λ _ → ≡⇒↝ _ $ cong (R ∘ (f _ ,_)) $
                                                                               lemma₂ eq₁ eq₂)) ⟩
  (∃ λ (eq₁ : x₁ ≡ y₁) →
   ∃ λ (eq₂ : x₂ ≡ y₂) →
   ∀ {o} →
   ((p : Position C₁ x₁ o) →
    R (f (inj₁ p) , g (inj₁ (subst (λ s₁ → Position C₁ s₁ o) eq₁ p))))
     ×
   ((p : Position C₂ x₂ o) →
    R (f (inj₂ p) , g (inj₂ (subst (λ s₂ → Position C₂ s₂ o) eq₂ p)))))   ↝⟨ (∃-cong λ _ → ∃-cong λ _ → implicit-ΠΣ-comm) ⟩

  (∃ λ (eq₁ : x₁ ≡ y₁) →
   ∃ λ (eq₂ : x₂ ≡ y₂) →
   (∀ {o} (p : Position C₁ x₁ o) →
    R (f (inj₁ p) , g (inj₁ (subst (λ s₁ → Position C₁ s₁ o) eq₁ p))))
     ×
   (∀ {o} (p : Position C₂ x₂ o) →
    R (f (inj₂ p) , g (inj₂ (subst (λ s₂ → Position C₂ s₂ o) eq₂ p)))))   ↝⟨ (∃-cong λ _ → ∃-comm) ⟩

  (∃ λ (eq₁ : x₁ ≡ y₁) →
   (∀ {o} (p : Position C₁ x₁ o) →
    R (f (inj₁ p) , g (inj₁ (subst (λ s₁ → Position C₁ s₁ o) eq₁ p))))
     ×
   ∃ λ (eq₂ : x₂ ≡ y₂) →
   (∀ {o} (p : Position C₂ x₂ o) →
    R (f (inj₂ p) , g (inj₂ (subst (λ s₂ → Position C₂ s₂ o) eq₂ p)))))   ↝⟨ Σ-assoc ⟩

  (∃ λ (eq : x₁ ≡ y₁) →
   (∀ {o} (p : Container.Position C₁ x₁ o) →
    R ( f (inj₁ p)
      , g (inj₁ (subst (λ s₁ → Container.Position C₁ s₁ o) eq p)))
      ))
    ×
  (∃ λ (eq : x₂ ≡ y₂) →
   (∀ {o} (p : Container.Position C₂ x₂ o) →
    R ( f (inj₂ p)
      , g (inj₂ (subst (λ s₂ → Container.Position C₂ s₂ o) eq p))
      )))                                                                 ↔⟨⟩

  ⟦ C₁ ⟧₂ R ((x₁ , f ∘ inj₁) , (y₁ , g ∘ inj₁))
    ×
  ⟦ C₂ ⟧₂ R ((x₂ , f ∘ inj₂) , (y₂ , g ∘ inj₂))                           □

  where
  open Container

  lemma₁ = λ (eq₁ : x₁ ≡ y₁) (eq₂ : x₂ ≡ y₂) {o p} →

    g (subst (λ { (s₁ , s₂) → Position C₁ s₁ o ⊎ Position C₂ s₂ o })
             (cong₂ _,_ eq₁ eq₂) (inj₁ p))                            ≡⟨ cong g $ push-subst-inj₁ {y≡z = cong₂ _,_ eq₁ eq₂} _ _ ⟩

    g (inj₁ (subst (λ { (s₁ , s₂) → Position C₁ s₁ o })
                   (cong₂ _,_ eq₁ eq₂) p))                            ≡⟨ cong (g ∘ inj₁) $ subst-∘ _ _ (cong₂ _,_ eq₁ eq₂) ⟩

    g (inj₁ (subst (λ s₁ → Position C₁ s₁ o)
                   (cong proj₁ (cong₂ _,_ eq₁ eq₂)) p))               ≡⟨ cong (g ∘ inj₁) $ cong (flip (subst _) _) $ cong-proj₁-cong₂-, eq₁ eq₂ ⟩∎

    g (inj₁ (subst (λ s₁ → Position C₁ s₁ o) eq₁ p))                  ∎

  lemma₂ = λ (eq₁ : x₁ ≡ y₁) (eq₂ : x₂ ≡ y₂) {o p} →

    g (subst (λ { (s₁ , s₂) → Position C₁ s₁ o ⊎ Position C₂ s₂ o })
             (cong₂ _,_ eq₁ eq₂) (inj₂ p))                            ≡⟨ cong g $ push-subst-inj₂ {y≡z = cong₂ _,_ eq₁ eq₂} _ _ ⟩

    g (inj₂ (subst (λ { (s₁ , s₂) → Position C₂ s₂ o })
                   (cong₂ _,_ eq₁ eq₂) p))                            ≡⟨ cong (g ∘ inj₂) $ subst-∘ _ _ (cong₂ _,_ eq₁ eq₂) ⟩

    g (inj₂ (subst (λ s₂ → Position C₂ s₂ o)
                   (cong proj₂ (cong₂ _,_ eq₁ eq₂)) p))               ≡⟨ cong (g ∘ inj₂) $ cong (flip (subst _) _) $ cong-proj₂-cong₂-, eq₁ eq₂ ⟩∎

    g (inj₂ (subst (λ s₂ → Position C₂ s₂ o) eq₂ p))                  ∎
