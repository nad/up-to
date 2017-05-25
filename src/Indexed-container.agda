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
open import Function-universe equality-with-J hiding (id; _∘_)
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

-- Some preservation lemmas.

⟦⟧₁-cong : ∀ {k ℓ₁ ℓ₂ ℓ₃} {I : Set ℓ₁} {C : Container₁ I}
             {A : Rel ℓ₂ I} {B : Rel ℓ₃ I} →
           (∀ {i} → A i ↝[ k ] B i) → ⟦ C ⟧₁ A ↝[ k ] ⟦ C ⟧₁ B
⟦⟧₁-cong {C = S ◁₁ P} {A} {B} A↝B =
  (∃ λ (s : S) → P s ⊆ A)  ↝⟨ (∃-cong λ _ → implicit-∀-cong ext $ ∀-cong ext λ _ → A↝B) ⟩□
  (∃ λ (s : S) → P s ⊆ B)  □

⟦_⟧-cong : ∀ {k ℓ₁ ℓ₂ ℓ₃} {I O : Set ℓ₁} (C : Container I O)
             {A : Rel ℓ₂ I} {B : Rel ℓ₃ I} →
           (∀ {i} → A i ↝[ k ] B i) →
           (∀ {o} → ⟦ C ⟧ A o ↝[ k ] ⟦ C ⟧ B o)
⟦ C ⟧-cong {A} {B} A↝B {o} =
  ⟦ C ⟧ A o   ↔⟨⟩
  ⟦ C o ⟧₁ A  ↝⟨ ⟦⟧₁-cong A↝B ⟩
  ⟦ C o ⟧₁ B  ↔⟨⟩
  ⟦ C ⟧ B o   □

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
    ∀ {ℓ₁ ℓ₂} {I : Set ℓ₁} (C : Container I I) {X : Rel ℓ₂ I} {i} →
    X ⊆ ⟦ C ⟧ X →
    X ⊆ ν C i
  unfold C f x = map C (unfold′ C f) (f x)

  unfold′ :
    ∀ {ℓ₁ ℓ₂} {I : Set ℓ₁} (C : Container I I) {X : Rel ℓ₂ I} {i} →
    X ⊆ ⟦ C ⟧ X →
    X ⊆ ν′ C i
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
    , record { force = map C (unfold′ C f) (f x) }
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
