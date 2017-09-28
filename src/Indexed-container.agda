------------------------------------------------------------------------
-- Indexed containers
------------------------------------------------------------------------

-- Some parts are based on "Indexed containers" by Altenkirch, Ghani,
-- Hancock, McBride and Morris (JFP, 2015).

{-# OPTIONS --without-K #-}

module Indexed-container where

open import Equality.Propositional
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

-- Doubly indexed containers.

record Container {ℓ} (I O : Set ℓ) : Set (lsuc ℓ) where
  constructor _◁_
  field
    Shape    : Rel ℓ O
    Position : ∀ {o} → Shape o → Rel ℓ I

-- Interpretation of containers.

⟦_⟧ : ∀ {ℓ₁ ℓ₂} {I O : Set ℓ₁} →
      Container I O → Rel ℓ₂ I → Rel (ℓ₁ ⊔ ℓ₂) O
⟦ S ◁ P ⟧ A = λ o → ∃ λ (s : S o) → P s ⊆ A

-- A map function.

map : ∀ {ℓ₁ ℓ₂ ℓ₃} {I O : Set ℓ₁} (C : Container I O)
        {A : Rel ℓ₂ I} {B : Rel ℓ₃ I} →
      A ⊆ B → ⟦ C ⟧ A ⊆ ⟦ C ⟧ B
map _ f (s , g) = (s , f ∘ g)

-- Functor laws.

map-id : ∀ {ℓ₁ ℓ₂} {I O : Set ℓ₁} {C : Container I O} {A : Rel ℓ₂ I} →
         _≡_ {A = ⟦ C ⟧ A ⊆ _} (map C id) id
map-id = refl

map-∘ : ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄} {I O : Set ℓ₁} {C : Container I O}
          {D : Rel ℓ₂ I} {E : Rel ℓ₃ I} {F : Rel ℓ₄ I}
        (f : E ⊆ F) (g : D ⊆ E) →
        _≡_ {A = ⟦ C ⟧ D ⊆ _} (map C (f ∘ g)) (map C f ∘ map C g)
map-∘ _ _ = refl

-- A preservation lemma.

⟦⟧-cong : ∀ {k ℓ₁ ℓ₂ ℓ₃} {I O : Set ℓ₁} →
          Extensionality? k ℓ₁ (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃) →
          (C : Container I O) {A : Rel ℓ₂ I} {B : Rel ℓ₃ I} →
          (∀ {i} → A i ↝[ k ] B i) →
          (∀ {o} → ⟦ C ⟧ A o ↝[ k ] ⟦ C ⟧ B o)
⟦⟧-cong ext (S ◁ P) {A} {B} A↝B {o} =
  (∃ λ (s : S o) → P s ⊆ A)  ↝⟨ (∃-cong λ _ → ⊆-congʳ ext A↝B) ⟩□
  (∃ λ (s : S o) → P s ⊆ B)  □

------------------------------------------------------------------------
-- Least fixpoints

mutual

  -- The least fixpoint of an indexed "endocontainer", expressed using
  -- sized types.

  μ : ∀ {ℓ} {X : Set ℓ} → Container X X → Size → Rel ℓ X
  μ C i = ⟦ C ⟧ (μ′ C i)

  data μ′ {ℓ} {X : Set ℓ}
          (C : Container X X) (i : Size) (x : X) : Set ℓ where
    ⟨_⟩ : {j : Size< i} → μ C j x → μ′ C i x

-- An inverse of ⟨_⟩ (for fully defined values).

⟨_⟩⁻¹ :
  ∀ {ℓ} {X : Set ℓ} {C : Container X X} →
  μ′ C ∞ ⊆ μ C ∞
⟨ ⟨ x ⟩ ⟩⁻¹ = x

-- The least fixpoint is a post-fixpoint.

μ-out :
  ∀ {ℓ} {X : Set ℓ} {C : Container X X} →
  μ C ∞ ⊆ ⟦ C ⟧ (μ C ∞)
μ-out {C = C} = map C ⟨_⟩⁻¹

-- The greatest fixpoint is a pre-fixpoint.

μ-in :
  ∀ {ℓ} {X : Set ℓ} {C : Container X X} →
  ⟦ C ⟧ (μ C ∞) ⊆ μ C ∞
μ-in {C = C} = map C ⟨_⟩

-- The least fixpoint is smaller than or equal to every
-- pre-fixpoint.

fold :
  ∀ {ℓ₁ ℓ₂} {X : Set ℓ₁} (C : Container X X) {A : Rel ℓ₂ X} →
  ⟦ C ⟧ A ⊆ A →
  ∀ {i} → μ C i ⊆ A
fold C f a = f (map C (λ { ⟨ a ⟩ → fold C f a }) a)

------------------------------------------------------------------------
-- Greatest fixpoints

mutual

  -- The greatest fixpoint of an indexed "endocontainer", expressed
  -- using sized types.

  ν : ∀ {ℓ} {X : Set ℓ} → Container X X → Size → Rel ℓ X
  ν C i = ⟦ C ⟧ (ν′ C i)

  record ν′ {ℓ} {X : Set ℓ}
            (C : Container X X) (i : Size) (x : X) : Set ℓ where
    coinductive
    field
      force : {j : Size< i} → ν C j x

open ν′ public

-- The greatest fixpoint ν C ∞ is a post-fixpoint.

ν-out :
  ∀ {ℓ} {X : Set ℓ} {i} {j : Size< i} (C : Container X X) →
  ν C i ⊆ ⟦ C ⟧ (ν C j)
ν-out C = map C (λ x → force x)

private

  ν-out-∞ :
    ∀ {ℓ} {X : Set ℓ} (C : Container X X) →
    ν C ∞ ⊆ ⟦ C ⟧ (ν C ∞)
  ν-out-∞ = ν-out

-- The greatest fixpoint is a pre-fixpoint.

ν-in :
  ∀ {ℓ} {X : Set ℓ} {i} (C : Container X X) →
  ⟦ C ⟧ (ν C i) ⊆ ν C i
ν-in C = map C (λ x → λ { .force → x })

-- The greatest fixpoint is greater than or equal to every
-- post-fixpoint.

unfold :
  ∀ {ℓ₁ ℓ₂} {X : Set ℓ₁} {A : Rel ℓ₂ X} {i} (C : Container X X) →
  A ⊆ ⟦ C ⟧ A → A ⊆ ν C i
unfold C f = map C (λ a → λ { .force → unfold C f a }) ∘ f

-- A generalisation of unfold with more sized types.

sized-unfold :
  ∀ {ℓ₁ ℓ₂} {X : Set ℓ₁} (C : Container X X) (A : Size → Rel ℓ₂ X) →
  (∀ {i} {j : Size< i} → A i ⊆ ⟦ C ⟧ (A j)) →
  ∀ {i} {j : Size< i} → A i ⊆ ν C j
sized-unfold C A f =
  map C (λ a → λ { .force → sized-unfold C A f a }) ∘ f

------------------------------------------------------------------------
-- Bisimilarity

-- A container corresponding to bisimilarity for a given container.

Bisimilarity :
  ∀ {ℓ} {X : Set ℓ} {C : Container X X} →
  let P = ∃ λ x → ν C ∞ x × ν C ∞ x in
  Container P P
Bisimilarity {C = C} =
  (λ { (_ , (s₁ , _) , (s₂ , _)) → s₁ ≡ s₂ })
    ◁
  (λ { {o = _ , (s₁ , f₁) , (s₂ , f₂)} eq (x , x₁ , x₂) →
       ∃ λ (p : Container.Position C s₁ x) →
       x₁ ≡ force (f₁ p)
         ×
       x₂ ≡ force (f₂ (subst (λ s → Container.Position C s x) eq p)) })

-- Bisimilarity for ν.

ν-bisimilar :
  ∀ {ℓ} {X : Set ℓ} {C : Container X X} {x} →
  Size → Rel₂ ℓ (ν C ∞ x)
ν-bisimilar i p = ν Bisimilarity i (_ , p)

ν′-bisimilar :
  ∀ {ℓ} {X : Set ℓ} {C : Container X X} {x} →
  Size → Rel₂ ℓ (ν′ C ∞ x)
ν′-bisimilar i (x , y) = ν′ Bisimilarity i (_ , force x , force y)

-- Lifts a family of binary relations from X to ⟦ C ⟧ X.

⟦_⟧₂ :
  ∀ {ℓ₁ ℓ₂} {I O : Set ℓ₁} {A : Rel ℓ₂ I} (C : Container I O) →
  (∀ {i} → Rel₂ ℓ₁ (A i)) →
  ∀ {o} → Rel₂ ℓ₁ (⟦ C ⟧ A o)
⟦ C ⟧₂ R ((s , f) , (t , g)) =
  ∃ λ (eq : s ≡ t) →
  ∀ {o} (p : Position C s o) →
  R (f p , g (subst (λ s → Position C s o) eq p))
  where
  open Container

-- An alternative characterisation of bisimilarity.

ν-bisimilar↔ :
  ∀ {k ℓ} {X : Set ℓ} {C : Container X X} {x i} →
  Extensionality? k ℓ ℓ →
  (x y : ν C ∞ x) →
  ν-bisimilar i (x , y) ↝[ k ] ⟦ C ⟧₂ (ν′-bisimilar i) (x , y)
ν-bisimilar↔ {C = C} {i = i} ext (s₁ , f₁) (s₂ , f₂) =

  ν-bisimilar i ((s₁ , f₁) , (s₂ , f₂))                             ↔⟨⟩

  (∃ λ (eq : s₁ ≡ s₂) →
   ∀ {x} →
   (∃ λ (p : Position C s₁ (proj₁ x)) →
      proj₁ (proj₂ x) ≡ force (f₁ p) ×
      proj₂ (proj₂ x) ≡
        force (f₂ (subst (λ s → Position C s (proj₁ x)) eq p))) →
   ν′ Bisimilarity i x)                                             ↝⟨ ∃-cong lemma ⟩

  (∃ λ (eq : s₁ ≡ s₂) →
   ∀ {x} (p : Position C s₁ x) →
   ν′-bisimilar i (f₁ p , f₂ (subst (λ s → Position C s x) eq p)))  ↔⟨⟩

  ⟦ C ⟧₂ (ν′-bisimilar i) ((s₁ , f₁) , (s₂ , f₂))                   □

  where
  open Container

  lemma = λ eq →

    (∀ {x} →
     (∃ λ (p : Position C s₁ (proj₁ x)) →
      proj₁ (proj₂ x) ≡ force (f₁ p) ×
      proj₂ (proj₂ x) ≡
        force (f₂ (subst (λ s → Position C s (proj₁ x)) eq p))) →
     ν′ Bisimilarity i x)                                                 ↔⟨ Bijection.implicit-Π↔Π ⟩

    (∀ x →
     (∃ λ (p : Position C s₁ (proj₁ x)) →
      proj₁ (proj₂ x) ≡ force (f₁ p) ×
      proj₂ (proj₂ x) ≡
        force (f₂ (subst (λ s → Position C s (proj₁ x)) eq p))) →
     ν′ Bisimilarity i x)                                                 ↝⟨ (∀-cong ext λ _ → from-isomorphism currying) ⟩

    (∀ x (p : Position C s₁ (proj₁ x)) →
     proj₁ (proj₂ x) ≡ force (f₁ p) ×
     proj₂ (proj₂ x) ≡
       force (f₂ (subst (λ s → Position C s (proj₁ x)) eq p)) →
     ν′ Bisimilarity i x)                                                 ↝⟨ (∀-cong ext λ _ → ∀-cong ext λ _ → from-isomorphism currying) ⟩

    (∀ x (p : Position C s₁ (proj₁ x)) →
     proj₁ (proj₂ x) ≡ force (f₁ p) →
     proj₂ (proj₂ x) ≡
       force (f₂ (subst (λ s → Position C s (proj₁ x)) eq p)) →
     ν′ Bisimilarity i x)                                                 ↔⟨ currying ⟩

    (∀ x yz (p : Position C s₁ x) →
     proj₁ yz ≡ force (f₁ p) →
     proj₂ yz ≡ force (f₂ (subst (λ s → Position C s x) eq p)) →
     ν′ Bisimilarity i (x , yz))                                          ↝⟨ (∀-cong ext λ _ → from-isomorphism Π-comm) ⟩

    (∀ x (p : Position C s₁ x) yz →
     proj₁ yz ≡ force (f₁ p) →
     proj₂ yz ≡ force (f₂ (subst (λ s → Position C s x) eq p)) →
     ν′ Bisimilarity i (x , yz))                                          ↝⟨ (∀-cong ext λ _ → ∀-cong ext λ _ → from-isomorphism currying) ⟩

    (∀ x (p : Position C s₁ x) y z →
     y ≡ force (f₁ p) →
     z ≡ force (f₂ (subst (λ s → Position C s x) eq p)) →
     ν′ Bisimilarity i (x , y , z))                                       ↝⟨ (∀-cong ext λ _ → ∀-cong ext λ _ → ∀-cong ext λ _ →
                                                                              from-isomorphism Π-comm) ⟩
    (∀ x (p : Position C s₁ x) →
     ∀ y → y ≡ force (f₁ p) →
     ∀ z → z ≡ force (f₂ (subst (λ s → Position C s x) eq p)) →
     ν′ Bisimilarity i (x , y , z))                                       ↝⟨ (∀-cong ext λ _ → ∀-cong ext λ _ →
                                                                              from-isomorphism $ inverse currying) ⟩
    (∀ x (p : Position C s₁ x) →
     (y : ∃ λ y → y ≡ force (f₁ p)) →
     ∀ z → z ≡ force (f₂ (subst (λ s → Position C s x) eq p)) →
     ν′ Bisimilarity i (x , proj₁ y , z))                                 ↝⟨ (∀-cong ext λ _ → ∀-cong ext λ _ → drop-⊤-left-Π ext (
                                                                              _⇔_.to contractible⇔↔⊤ $ singleton-contractible _)) ⟩
    (∀ x (p : Position C s₁ x) →
     ∀ z → z ≡ force (f₂ (subst (λ s → Position C s x) eq p)) →
     ν′ Bisimilarity i (x , force (f₁ p) , z))                            ↝⟨ (∀-cong ext λ _ → ∀-cong ext λ _ →
                                                                              from-isomorphism $ inverse currying) ⟩
    (∀ x (p : Position C s₁ x) →
     (z : ∃ λ z → z ≡ force (f₂ (subst (λ s → Position C s x) eq p))) →
     ν′ Bisimilarity i (x , force (f₁ p) , proj₁ z))                      ↝⟨ (∀-cong ext λ _ → ∀-cong ext λ _ → drop-⊤-left-Π ext (
                                                                              _⇔_.to contractible⇔↔⊤ $ singleton-contractible _)) ⟩
    (∀ x (p : Position C s₁ x) →
     ν′ Bisimilarity i
       (x , force (f₁ p)
          , force (f₂ (subst (λ s → Position C s x) eq p))))              ↔⟨ inverse $ Bijection.implicit-Π↔Π ⟩

    (∀ {x} (p : Position C s₁ x) →
     ν′ Bisimilarity i
       (x , force (f₁ p)
          , force (f₂ (subst (λ s → Position C s x) eq p))))              ↔⟨⟩

    (∀ {x} (p : Position C s₁ x) →
     ν′-bisimilar i (f₁ p , f₂ (subst (λ s → Position C s x) eq p)))      □

module Bisimilarity
         {ℓ} {X : Set ℓ} {C : Container X X} {x i}
         (x y : ν C ∞ x)
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
  ⟨_,_,_,_⟩ = curry $ _⇔_.from (ν-bisimilar↔ _ x y)

  -- A "projection".

  split : ν-bisimilar i (x , y) → ⟦ C ⟧₂ (ν′-bisimilar i) (x , y)
  split = ν-bisimilar↔ _ x y

-- Bisimilarity is reflexive.

reflexive-ν :
  ∀ {ℓ} {X : Set ℓ} {C : Container X X} {x} (x : ν C ∞ x) {i} →
  ν-bisimilar i (x , x)
reflexive-ν x =
  Bisimilarity.⟨ x , x , refl
               , (λ { p .force → reflexive-ν (force (proj₂ x p)) })
               ⟩

-- Bisimilarity is symmetric.

symmetric-ν :
  ∀ {ℓ} {X : Set ℓ} {C : Container X X} {x} (x y : ν C ∞ x) {i} →
  ν-bisimilar i (x , y) → ν-bisimilar i (y , x)
symmetric-ν x y bisim with Bisimilarity.split x y bisim
... | refl , bisim′ =
  Bisimilarity.⟨ y , x , refl
               , (λ { p .force →
                      symmetric-ν (force (proj₂ x p))
                                  (force (proj₂ y p))
                                  (force (bisim′ p)) })
               ⟩

-- Bisimilarity is transitive.

transitive-ν :
  ∀ {ℓ} {X : Set ℓ} {C : Container X X} {x} (x y z : ν C ∞ x) {i} →
  ν-bisimilar i (x , y) → ν-bisimilar i (y , z) →
  ν-bisimilar i (x , z)
transitive-ν x y z bisim₁ bisim₂ with Bisimilarity.split x y bisim₁
                                    | Bisimilarity.split y z bisim₂
... | refl , bisim₁′ | refl , bisim₂′ =
  Bisimilarity.⟨ x
               , z
               , refl
               , (λ { p .force →
                      transitive-ν
                        (force (proj₂ x p))
                        (force (proj₂ y p))
                        (force (proj₂ z p))
                        (force (bisim₁′ p))
                        (force (bisim₂′ p)) })
               ⟩

-- Extensionality for ν′ C: bisimilarity implies equality.
--
-- TODO: Is this a consistent assumption?

ν′-extensionality : ∀ {ℓ} {X : Set ℓ} → Container X X → Set ℓ
ν′-extensionality C =
  ∀ {x} {y z : ν′ C ∞ x} → ν′-bisimilar ∞ (y , z) → y ≡ z

-- The formulation of extensionality given above for ν′ can be used to
-- derive a form of extensionality for ν (in the presence of
-- extensionality for functions).

ν-extensionality :
  ∀ {ℓ} {X : Set ℓ} {C : Container X X} →
  Extensionality ℓ ℓ →
  ν′-extensionality C →
  ∀ {x} {y z : ν C ∞ x} → ν-bisimilar ∞ (y , z) → y ≡ z
ν-extensionality {C = C} ext ν′-ext
                 {y = y@(s , f₁)} {z = z@(.s , f₂)} bisim@(refl , _) =

                                                             $⟨ (λ _ → proj₂ $ Bisimilarity.split y z bisim) ⟩
  (∀ x (p : Position C s x) → ν′-bisimilar ∞ (f₁ p , f₂ p))  ↝⟨ (ν′-ext ∘_) ∘_ ⟩
  (∀ x (p : Position C s x) → f₁ p ≡ f₂ p)                   ↝⟨ implicit-extensionality ext ∘ (apply-ext ext ∘_) ⟩
  (λ {_} → f₁) ≡ f₂                                          ↝⟨ cong (s ,_) ⟩□
  y ≡ z                                                      □

  where
  open Container

------------------------------------------------------------------------
-- More properties related to ν and ν′

-- The greatest fixpoint is a fixpoint in a different sense
-- (assuming two kinds of extensionality and univalence).

ν-fixpoint :
  ∀ {ℓ} →
  Extensionality ℓ (lsuc ℓ) →
  Univalence ℓ →
  {X : Set ℓ} (C : Container X X) →
  ν′-extensionality C →
  ν C ∞ ≡ ⟦ C ⟧ (ν C ∞)
ν-fixpoint ext univ C ν′-ext =
  ν C ∞           ≡⟨⟩
  ⟦ C ⟧ (ν′ C ∞)  ≡⟨ cong ⟦ C ⟧ (apply-ext ext λ _ → ≃⇒≡ univ (Eq.↔⇒≃ ν′↔ν)) ⟩
  ⟦ C ⟧ (ν C ∞)   ∎
  where
  ν′↔ν : ∀ {x} → ν′ C ∞ x ↔ ν C ∞ x
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

-- The unfold function makes a certain diagram commute.

unfold-commute :
  ∀ {ℓ₁ ℓ₂} {X : Set ℓ₁} (C : Container X X) {A : Rel ℓ₂ X}
  (f : A ⊆ ⟦ C ⟧ A) →
  ∀ {i x} (a : A x) →
  ν-bisimilar i
    ( unfold C f a
    , ν-in C (map C (unfold C f) (f a))
    )
unfold-commute C f a =
  Bisimilarity.⟨ unfold C f a
               , ν-in C (map C (unfold C f) (f a))
               , refl
               , (λ { p .force →
                      reflexive-ν (unfold C f (proj₂ (f a) p)) })
               ⟩

-- A uniqueness property for unfold.

unfold-unique :
  ∀ {ℓ₁ ℓ₂} {X : Set ℓ₁} (C : Container X X) {A : Rel ℓ₂ X}
  (f : A ⊆ ⟦ C ⟧ A) (u : A ⊆ ν C ∞) {i} →
  (∀ {x} (a : A x) →
   ν-bisimilar i (u a , ν-in C (map C u (f a)))) →
  ∀ {x} (a : A x) → ν-bisimilar i (u a , unfold C f a)
unfold-unique C f u bisim a
  with Bisimilarity.split (u a) (ν-in C (map C u (f a))) (bisim a)
... | eq , bisim′ =
  Bisimilarity.⟨ u a
               , unfold C f a
               , eq
               , (λ { p .force →
                      let p′ = subst (λ s → Container.Position C s _)
                                     eq p in
                      transitive-ν
                        (force (proj₂ (u a) p))
                        (force (proj₂ (ν-in C (map C u (f a))) p′))
                        (force (proj₂ (unfold C f a) p′))
                        (force (bisim′ p))
                        (unfold-unique C f u bisim _) })
               ⟩

------------------------------------------------------------------------
-- An alternative definition of greatest fixpoints

-- The greatest fixpoint of an indexed "endocontainer" (parametrised
-- by a universe level).

gfp : ∀ {ℓ₁} ℓ₂ {X : Set ℓ₁} → Container X X → Rel (lsuc (ℓ₁ ⊔ ℓ₂)) X
gfp {ℓ₁} ℓ₂ {X} C x = ∃ λ (R : Rel (ℓ₁ ⊔ ℓ₂) X) → R ⊆ ⟦ C ⟧ R × R x

-- The greatest fixpoint is greater than or equal to every
-- sufficiently small post-fixpoint.

gfp-unfold :
  ∀ {ℓ₁ ℓ₂} ℓ₃ {X : Set ℓ₁} {C : Container X X} {A : Rel ℓ₂ X} →
  A ⊆ ⟦ C ⟧ A →
  A ⊆ gfp (ℓ₂ ⊔ ℓ₃) C
gfp-unfold {ℓ₁} ℓ₃ {C = C} {A} f a =
  ↑ (ℓ₁ ⊔ ℓ₃) ∘ A , map C lift ∘ f ∘ lower , lift a

-- The greatest fixpoint is a post-fixpoint.

gfp-out : ∀ {ℓ₁} ℓ₂ {X : Set ℓ₁} {C : Container X X} →
          gfp ℓ₂ C ⊆ ⟦ C ⟧ (gfp ℓ₂ C)
gfp-out ℓ₂ {C = C} (R , R⊆CR , Ri) =
  map C (λ Ri → R , (λ {_} → R⊆CR) , Ri) (R⊆CR Ri)

  -- It is possible to use gfp-unfold ℓ₂ R⊆CR as the second argument
  -- to map above. However, the extra lifting would break the proof
  -- gfp⊆ν∘ν⊆gfp given below.

-- The first definition of greatest fixpoints is contained in the
-- second one.

ν⊆gfp : ∀ {ℓ₁} ℓ₂ {X : Set ℓ₁} {C : Container X X} →
        ν C ∞ ⊆ gfp ℓ₂ C
ν⊆gfp ℓ₂ = gfp-unfold ℓ₂ (ν-out {i = ∞} _)

-- The second definition of greatest fixpoints is contained in the first one.

gfp⊆ν : ∀ {ℓ₁} ℓ₂ {X : Set ℓ₁} {C : Container X X} {i} →
        gfp ℓ₂ C ⊆ ν C i
gfp⊆ν ℓ₂ = unfold _ (gfp-out ℓ₂)

-- Thus the two definitions of greatest fixpoints are pointwise
-- logically equivalent.

gfp⇔ν : ∀ {ℓ₁} ℓ₂ {X : Set ℓ₁} {C : Container X X} {i} →
        gfp ℓ₂ C i ⇔ ν C ∞ i
gfp⇔ν ℓ₂ = record
  { to   = gfp⊆ν ℓ₂
  ; from = ν⊆gfp ℓ₂
  }

-- The function gfp⊆ν is a left inverse of ν⊆gfp (up to pointwise
-- bisimilarity).

gfp⊆ν∘ν⊆gfp :
  ∀ {ℓ₁} ℓ₂ {X : Set ℓ₁} {C : Container X X} {x} (x : ν C ∞ x) {i} →
  ν-bisimilar i (gfp⊆ν ℓ₂ (ν⊆gfp ℓ₂ x) , x)
gfp⊆ν∘ν⊆gfp ℓ₂ {C = C} x =
  _⇔_.from (ν-bisimilar↔ _ (gfp⊆ν ℓ₂ (ν⊆gfp ℓ₂ x)) x)
    ( refl
    , (λ { p .force → gfp⊆ν∘ν⊆gfp ℓ₂ (force (proj₂ x p)) })
    )

-- There is a split surjection from the second definition of greatest
-- fixpoints to the first one (assuming two kinds of extensionality).

gfp↠ν :
  ∀ {ℓ₁} →
  Extensionality ℓ₁ ℓ₁ →
  ∀ ℓ₂ {X : Set ℓ₁} {C : Container X X} →
  ν′-extensionality C →
  ∀ {x} → gfp ℓ₂ C x ↠ ν C ∞ x
gfp↠ν ext ℓ₂ ν′-ext = record
  { logical-equivalence = gfp⇔ν ℓ₂
  ; right-inverse-of    = λ x →
      ν-extensionality ext ν′-ext (gfp⊆ν∘ν⊆gfp ℓ₂ x)
  }

-- The larger versions of gfp are logically equivalent to the smallest
-- one.

larger⇔smallest :
  ∀ {ℓ₁} ℓ₂ {X : Set ℓ₁} {C : Container X X} {x} →
  gfp ℓ₂ C x ⇔ gfp lzero C x
larger⇔smallest ℓ₂ {C = C} {x} =
  gfp ℓ₂ C x     ↝⟨ gfp⇔ν ℓ₂ ⟩
  ν C ∞ x        ↝⟨ inverse $ gfp⇔ν lzero ⟩□
  gfp lzero C x  □
