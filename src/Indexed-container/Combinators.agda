------------------------------------------------------------------------
-- Container combinators
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Indexed-container.Combinators where

open import Equality.Propositional
open import Logical-equivalence using (_⇔_)
open import Prelude as P hiding (id; const) renaming (_∘_ to _⊚_)

open import Bijection equality-with-J as Bijection using (_↔_)
open import Equivalence equality-with-J hiding (id; _∘_; inverse)
open import Function-universe equality-with-J as F hiding (id; _∘_)

open import Indexed-container
open import Relation

-- An identity combinator.
--
-- Taken from "Indexed containers" by Altenkirch, Ghani, Hancock,
-- McBride and Morris (JFP, 2015).

id : ∀ {i} {I : Set i} → Container I I
id i = ↑ _ ⊤ ◁₁ λ _ i′ → i ≡ i′

-- An unfolding lemma for ⟦ id ⟧.

⟦id⟧↔ : ∀ {k ℓ x} {I : Set ℓ} {X : Rel x I} {i} →
        Extensionality? k ℓ (ℓ ⊔ x) →
        ⟦ id ⟧ X i ↝[ k ] X i
⟦id⟧↔ {X = X} {i} ext =
  ↑ _ ⊤ × (λ i′ → i ≡ i′) ⊆ X  ↔⟨ drop-⊤-left-× (λ _ → Bijection.↑↔) ⟩
  (λ i′ → i ≡ i′) ⊆ X          ↔⟨⟩
  (∀ {i′} → i ≡ i′ → X i′)     ↔⟨ Bijection.implicit-Π↔Π ⟩
  (∀ i′ → i ≡ i′ → X i′)       ↝⟨ inverse-ext? (λ ext → ∀-intro ext _) ext ⟩□
  X i                          □

-- An unfolding lemma for ⟦ id ⟧₂.

⟦id⟧₂↔ :
  ∀ {k ℓ x} {I : Set ℓ} {X : Rel x I} →
  Extensionality? k ℓ ℓ →
  ∀ (R : ∀ {i} → Rel₂ ℓ (X i)) {i} →
  (x y : ⟦ id ⟧ X i) →

  ⟦ id ⟧₂ R (x , y)
    ↝[ k ]
  proj₁ x ≡ proj₁ y × R (proj₂ x refl , proj₂ y refl)

⟦id⟧₂↔ ext R {i} x@(s , f) y@(t , g) =

  ⟦ id ⟧₂ R (x , y)                               ↔⟨⟩

  (∃ λ (eq : s ≡ t) →
   ∀ {o} (p : i ≡ o) →
   R (f p , g (subst (λ _ → i ≡ o) eq p)))        ↔⟨ ∃-cong (λ _ → Bijection.implicit-Π↔Π) ⟩

  (∃ λ (eq : s ≡ t) →
   ∀ o (p : i ≡ o) →
   R (f p , g (subst (λ _ → i ≡ o) eq p)))        ↝⟨ ∃-cong (λ _ → inverse-ext? (λ ext → ∀-intro ext _) ext) ⟩

  (∃ λ (eq : s ≡ t) →
   R (f refl , g (subst (λ _ → i ≡ i) eq refl)))  ↝⟨ ∃-cong (λ eq → ≡⇒↝ _ (cong (λ eq → R (f refl , g eq)) (subst-const eq))) ⟩

  s ≡ t × R (f refl , g refl)                     □

-- A second unfolding lemma for ⟦ id ⟧₂.

⟦id⟧₂≡↔ :
  ∀ {ℓ} {I : Set ℓ} {X : Rel ℓ I} {i} →
  Extensionality ℓ ℓ →
  (x y : ⟦ id ⟧ X i) →
  ⟦ id ⟧₂ (uncurry _≡_) (x , y) ↔ x ≡ y
⟦id⟧₂≡↔ ext x@(s , f) y@(t , g) =

  ⟦ id ⟧₂ (uncurry _≡_) (x , y)  ↝⟨ ⟦id⟧₂↔ ext (uncurry _≡_) x y ⟩

  s ≡ t × f refl ≡ g refl        ↔⟨ ∃-cong (λ _ → ≃-≡ (↔⇒≃ $ inverse $ ∀-intro ext _)) ⟩

  s ≡ t × (λ _ → f) ≡ (λ _ → g)  ↔⟨ ∃-cong (λ _ → ≃-≡ (↔⇒≃ Bijection.implicit-Π↔Π)) ⟩

  s ≡ t × (λ {_} → f) ≡ g        ↝⟨ ≡×≡↔≡ ⟩

  x ≡ y                          □

-- A constant combinator.

const : ∀ {i} {I : Set i} → Rel i I → Container I I
const X = X ◁ λ _ _ → ⊥

-- An unfolding lemma for ⟦ const ⟧.

⟦const⟧↔ : ∀ {k ℓ y} {I : Set ℓ} {X} {Y : Rel y I} {i} →
           Extensionality? k ℓ (ℓ ⊔ y) →
           ⟦ const X ⟧ Y i ↝[ k ] X i
⟦const⟧↔ {k} {ℓ} {I = I} {X} {Y} {i} ext =
  X i × (∀ {i} → ⊥ → Y i)  ↔⟨ ∃-cong (λ _ → Bijection.implicit-Π↔Π) ⟩
  X i × (∀ i → ⊥ → Y i)    ↝⟨ ∃-cong (λ _ → ∀-cong ext λ _ → Π⊥↔⊤ (lower-extensionality? k lzero ℓ ext)) ⟩
  X i × (I → ⊤)            ↔⟨ drop-⊤-right (λ _ → →-right-zero) ⟩
  X i                      □

-- An unfolding lemma for ⟦ const ⟧₂.

⟦const⟧₂↔ :
  ∀ {k ℓ y} {I : Set ℓ} {X} {Y : Rel y I} →
  Extensionality? k ℓ ℓ →
  ∀ (R : ∀ {i} → Rel₂ ℓ (Y i)) {i}
  (x y : ⟦ const X ⟧ Y i) →

  ⟦ const X ⟧₂ R (x , y)
    ↝[ k ]
  proj₁ x ≡ proj₁ y

⟦const⟧₂↔ {X = X} ext R x@(s , f) y@(t , g) =

  ⟦ const X ⟧₂ R (x , y)                                ↔⟨⟩

  (∃ λ (eq : s ≡ t) →
   ∀ {o} (p : ⊥) → R (f p , g (subst (λ _ → ⊥) eq p)))  ↔⟨ ∃-cong (λ _ → Bijection.implicit-Π↔Π) ⟩

  (∃ λ (eq : s ≡ t) →
   ∀ o (p : ⊥) → R (f p , g (subst (λ _ → ⊥) eq p)))    ↝⟨ ∃-cong (λ _ → ∀-cong ext λ _ → Π⊥↔⊤ ext) ⟩

  (∃ λ (eq : s ≡ t) → ∀ o → ⊤)                          ↔⟨ drop-⊤-right (λ _ → →-right-zero) ⟩

  s ≡ t                                                 □

  where
  open Container

-- A composition combinator.

infixr 9 _∘_

_∘_ : ∀ {ℓ} {I J K : Set ℓ} →
      Container J K → Container I J → Container I K
C ∘ D =
  ⟦ C ⟧ (Shape D)
    ◁
  (λ { (s , f) i →
       ∃ λ j → ∃ λ (p : Position C s j) → Position D (f p) i })
  where
  open Container

-- An unfolding lemma for ⟦ C ∘ D ⟧.

⟦∘⟧↔ : ∀ {fk ℓ x} {I J K : Set ℓ} {X : Rel x I} →
       Extensionality? fk ℓ (ℓ ⊔ x) →
       ∀ (C : Container J K) {D : Container I J} {k} →
       ⟦ C ∘ D ⟧ X k ↝[ fk ] ⟦ C ⟧ (⟦ D ⟧ X) k
⟦∘⟧↔ {X = X} ext C {D} {k} =

  ⟦ C ∘ D ⟧ X k                                                     ↔⟨⟩

  (∃ λ { (s , f) →
         ∀ {i} →
         (∃ λ j → ∃ λ (p : Position C s j) → Position D (f p) i) →
         X i })                                                     ↔⟨ inverse Σ-assoc ⟩

  (∃ λ s →
   ∃ λ (f : Position C s ⊆ Shape D) →
     ∀ {i} →
     (∃ λ j → ∃ λ (p : Position C s j) → Position D (f p) i) →
     X i)                                                           ↝⟨ (∃-cong λ _ → ∃-cong λ _ → implicit-∀-cong ext $
                                                                        from-isomorphism currying) ⟩
  (∃ λ s →
   ∃ λ (f : Position C s ⊆ Shape D) →
     ∀ {i} j →
     (∃ λ (p : Position C s j) → Position D (f p) i) →
     X i)                                                           ↔⟨ (∃-cong λ _ → ∃-cong λ _ → Bijection.implicit-Π↔Π) ⟩

  (∃ λ s →
   ∃ λ (f : Position C s ⊆ Shape D) →
     ∀ i j →
     (∃ λ (p : Position C s j) → Position D (f p) i) →
     X i)                                                           ↔⟨ (∃-cong λ _ → ∃-cong λ _ → Π-comm) ⟩

  (∃ λ s →
   ∃ λ (f : Position C s ⊆ Shape D) →
     ∀ j i →
     (∃ λ (p : Position C s j) → Position D (f p) i) →
     X i)                                                           ↔⟨ (∃-cong λ _ → ∃-cong λ _ → inverse Bijection.implicit-Π↔Π) ⟩

  (∃ λ s →
   ∃ λ (f : Position C s ⊆ Shape D) →
     ∀ {j} i →
     (∃ λ (p : Position C s j) → Position D (f p) i) →
     X i)                                                           ↔⟨ (∃-cong λ _ → inverse implicit-ΠΣ-comm) ⟩

  (∃ λ s → ∀ {j} →
   ∃ λ (f : Position C s j → Shape D j) →
     ∀ i →
     (∃ λ (p : Position C s j) → Position D (f p) i) →
     X i)                                                           ↝⟨ (∃-cong λ _ → implicit-∀-cong ext $ ∃-cong λ _ → ∀-cong ext λ _ →
                                                                        from-isomorphism currying) ⟩
  (∃ λ s → ∀ {j} →
   ∃ λ (f : Position C s j → Shape D j) →
     ∀ i → (p : Position C s j) → Position D (f p) i → X i)         ↝⟨ (∃-cong λ _ → implicit-∀-cong ext $ ∃-cong λ _ → from-isomorphism Π-comm) ⟩

  (∃ λ s → ∀ {j} →
   ∃ λ (f : Position C s j → Shape D j) →
     (p : Position C s j) → ∀ i → Position D (f p) i → X i)         ↝⟨ (∃-cong λ _ → implicit-∀-cong ext $ from-isomorphism $ inverse ΠΣ-comm) ⟩

  (∃ λ s → ∀ {j} → Position C s j →
   ∃ λ (s′ : Shape D j) → ∀ i → Position D s′ i → X i)              ↝⟨ (∃-cong λ _ → implicit-∀-cong ext $ ∀-cong ext λ _ → ∃-cong λ _ →
                                                                        from-isomorphism $ inverse Bijection.implicit-Π↔Π) ⟩
  (∃ λ s → ∀ {j} → Position C s j →
   ∃ λ (s′ : Shape D j) → Position D s′ ⊆ X)                        ↔⟨⟩

  ⟦ C ⟧ (⟦ D ⟧ X) k                                                 □

  where
  open Container

-- TODO: Define ⟦∘⟧₂↔ (an unfolding lemma for ⟦ C ∘ D ⟧₂).

-- A reindexing combinator.
--
-- Taken from "Indexed containers".

reindex₂ : ∀ {ℓ} {I O₁ O₂ : Set ℓ} →
           (O₂ → O₁) → Container I O₁ → Container I O₂
reindex₂ f C = C ⊚ f

-- An unfolding lemma for ⟦ reindex₂ f C ⟧.

⟦reindex₂⟧↔ : ∀ {ℓ x} {I O₁ O₂ : Set ℓ} (f : O₂ → O₁)
              (C : Container I O₁) {X : Rel x I} {o} →
              ⟦ reindex₂ f C ⟧ X o ↔ ⟦ C ⟧ X (f o)
⟦reindex₂⟧↔ f C = Bijection.id

-- An unfolding lemma for ⟦ reindex₂ f C ⟧₂.

⟦reindex₂⟧₂↔ :
  ∀ {ℓ x} {I O : Set ℓ} {X : Rel x I}
  (C : Container I O) (f : I → O) (R : ∀ {i} → Rel₂ ℓ (X i)) {i}
  (x y : ⟦ reindex₂ f C ⟧ X i) →

  ⟦ reindex₂ f C ⟧₂ R (x , y) ↔ ⟦ C ⟧₂ R (x , y)

⟦reindex₂⟧₂↔ C f R x@(s , g) y@(t , h) =

  ⟦ reindex₂ f C ⟧₂ R (x , y)                              ↔⟨⟩

  (∃ λ (eq : s ≡ t) →
   ∀ {o} (p : Position (C ⊚ f) s o) →
   R (g p , h (subst (λ s → Position (C ⊚ f) s o) eq p)))  ↔⟨⟩

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

-- An unfolding lemma for ⟦ reindex₁ f C ⟧.

⟦reindex₁⟧↔ : ∀ {k ℓ x} {I₁ I₂ O : Set ℓ} {f : I₁ → I₂} →
              Extensionality? k ℓ (ℓ ⊔ x) →
              ∀ (C : Container I₁ O) {X : Rel x I₂} {o} →
              ⟦ reindex₁ f C ⟧ X o ↝[ k ] ⟦ C ⟧ (X ⊚ f) o
⟦reindex₁⟧↔ {f = f} ext C {X} {o} =
  ⟦ reindex₁ f C ⟧ X o                                 ↔⟨ (∃-cong λ _ → Bijection.implicit-Π↔Π) ⟩

  (∃ λ (s : Shape C o) →
   ∀ i → (∃ λ i′ → f i′ ≡ i × Position C s i′) → X i)  ↝⟨ (∃-cong λ _ → ∀-cong ext λ _ → from-isomorphism currying) ⟩

  (∃ λ (s : Shape C o) →
   ∀ i i′ → f i′ ≡ i × Position C s i′ → X i)          ↝⟨ (∃-cong λ _ → ∀-cong ext λ _ → ∀-cong ext λ _ → from-isomorphism currying) ⟩

  (∃ λ (s : Shape C o) →
   ∀ i i′ → f i′ ≡ i → Position C s i′ → X i)          ↔⟨ (∃-cong λ _ → Π-comm) ⟩

  (∃ λ (s : Shape C o) →
   ∀ i i′ → f i ≡ i′ → Position C s i → X i′)          ↝⟨ (∃-cong λ _ → ∀-cong ext λ _ → inverse-ext? (λ ext → ∀-intro ext _) ext) ⟩

  (∃ λ (s : Shape C o) →
   ∀ i → Position C s i → X (f i))                     ↔⟨ (∃-cong λ _ → inverse Bijection.implicit-Π↔Π) ⟩

  ⟦ C ⟧ (X ⊚ f) o                                      □
  where
  open Container

-- An unfolding lemma for ⟦ reindex₁ f C ⟧₂.

⟦reindex₁⟧₂↔ :
  ∀ {k ℓ x} {I O : Set ℓ} {X : Rel x O} →
  Extensionality? k ℓ ℓ →
  ∀ (C : Container I O) (f : I → O) (R : ∀ {o} → Rel₂ ℓ (X o)) {o}
  (x y : ⟦ reindex₁ f C ⟧ X o) →

  ⟦ reindex₁ f C ⟧₂ R (x , y)

    ↝[ k ]

  ⟦ C ⟧₂ R ( (proj₁ x , λ p → proj₂ x (_ , refl , p))
           , (proj₁ y , λ p → proj₂ y (_ , refl , p))
           )

⟦reindex₁⟧₂↔ ext C f R x@(s , g) y@(t , h) =

  ⟦ reindex₁ f C ⟧₂ R (x , y)                                             ↔⟨⟩

  (∃ λ (eq : s ≡ t) →
   ∀ {o} (p : ∃ λ o′ → f o′ ≡ o × Position C s o′) →
   R (g p , h (subst (λ s → ∃ λ o′ → f o′ ≡ o × Position C s o′) eq p)))  ↝⟨ (∃-cong λ eq → implicit-∀-cong ext $ ∀-cong ext λ _ →
                                                                              ≡⇒↝ _ $ cong (R ⊚ (g _ ,_) ⊚ h) $
                                                                              lemma eq) ⟩
  (∃ λ (eq : s ≡ t) →
   ∀ {o} (p : ∃ λ o′ → f o′ ≡ o × Position C s o′) →
   R ( g p
     , h ( proj₁ p
         , proj₁ (proj₂ p)
         , subst (λ s → Position C s (proj₁ p)) eq (proj₂ (proj₂ p))
         )
     ))                                                                   ↝⟨ (∃-cong λ _ → implicit-∀-cong ext $ from-isomorphism
                                                                              currying) ⟩
  (∃ λ (eq : s ≡ t) →
   ∀ {o} o′ (p : f o′ ≡ o × Position C s o′) →
   R ( g (o′ , p)
     , h (o′ , proj₁ p , subst (λ s → Position C s o′) eq (proj₂ p))
     ))                                                                   ↝⟨ (∃-cong λ _ → implicit-∀-cong ext $ ∀-cong ext λ _ → from-isomorphism
                                                                              currying) ⟩
  (∃ λ (eq : s ≡ t) →
   ∀ {o} o′ (≡o : f o′ ≡ o) (p : Position C s o′) →
   R ( g (o′ , ≡o , p)
     , h (o′ , ≡o , subst (λ s → Position C s o′) eq p)
     ))                                                                   ↔⟨ (∃-cong λ _ →
                                                                              Bijection.implicit-Π↔Π) ⟩
  (∃ λ (eq : s ≡ t) →
   ∀ o o′ (≡o : f o′ ≡ o) (p : Position C s o′) →
   R ( g (o′ , ≡o , p)
     , h (o′ , ≡o , subst (λ s → Position C s o′) eq p)
     ))                                                                   ↔⟨ (∃-cong λ _ →
                                                                              Π-comm) ⟩
  (∃ λ (eq : s ≡ t) →
   ∀ o o′ (≡o′ : f o ≡ o′) (p : Position C s o) →
   R ( g (o , ≡o′ , p)
     , h (o , ≡o′ , subst (λ s → Position C s o) eq p)
     ))                                                                   ↝⟨ (∃-cong λ _ → ∀-cong ext λ _ →
                                                                              inverse-ext? (λ ext → ∀-intro ext _) ext) ⟩
  (∃ λ (eq : s ≡ t) →
   ∀ o (p : Position C s o) →
   R ( g (o , refl , p)
     , h (o , refl , subst (λ s → Position C s o) eq p)
     ))                                                                   ↔⟨ (∃-cong λ _ → inverse
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
                                                                                          ((_≡ o) ⊚ f ⊚ proj₂) (uncurry (Position C)) ⟩
    ( proj₁ p
    , subst ((_≡ o) ⊚ f ⊚ proj₂)   (cong₂ _,_ eq refl) (proj₁ (proj₂ p))
    , subst (uncurry (Position C)) (cong₂ _,_ eq refl) (proj₂ (proj₂ p))
    )                                                                     ≡⟨ cong (λ eq′ → _ , eq′
                                                                                             , subst (uncurry (Position C)) (cong₂ _,_ eq refl) _) $
                                                                             subst-∘ ((_≡ o) ⊚ f) proj₂ (cong₂ _,_ eq refl) ⟩
    ( proj₁ p
    , subst ((_≡ o) ⊚ f)
            (cong proj₂ (cong₂ _,_ eq refl)) (proj₁ (proj₂ p))
    , subst (uncurry (Position C)) (cong (_, _) eq) (proj₂ (proj₂ p))
    )                                                                     ≡⟨ cong₂ (λ eq₁ eq₂ → _ , subst ((_≡ o) ⊚ f) eq₁ _ , eq₂)
                                                                             (cong-proj₂-cong₂-, eq refl)
                                                                             (sym $ subst-∘ (uncurry (Position C)) (_, _) eq) ⟩
    ( proj₁ p
    , subst ((_≡ o) ⊚ f) refl (proj₁ (proj₂ p))
    , subst (uncurry (Position C) ⊚ (_, _)) eq (proj₂ (proj₂ p))
    )                                                                     ≡⟨⟩

    ( proj₁ p
    , proj₁ (proj₂ p)
    , subst (λ s → Position C s (proj₁ p)) eq (proj₂ (proj₂ p))
    )                                                                     ∎

-- A combined reindexing combinator.
--
-- The application reindex swap is similar to the overline function
-- from Section 6.3.4.1 in Pous and Sangiorgi's "Enhancements of the
-- bisimulation proof method".

reindex : ∀ {ℓ} {I O : Set ℓ} →
          (I → O) → Container I O → Container O I
reindex f = reindex₂ f ⊚ reindex₁ f

-- An unfolding lemma for ⟦ reindex f C ⟧.

⟦reindex⟧↔ : ∀ {k ℓ x} {I O : Set ℓ} {f : I → O} →
             Extensionality? k ℓ (ℓ ⊔ x) →
             ∀ (C : Container I O) {X : Rel x O} {i} →
             ⟦ reindex f C ⟧ X i ↝[ k ] ⟦ C ⟧ (X ⊚ f) (f i)
⟦reindex⟧↔ {f = f} ext C {X} {i} =
  ⟦ reindex f C ⟧ X i                ↔⟨⟩
  ⟦ reindex₂ f (reindex₁ f C) ⟧ X i  ↔⟨⟩
  ⟦ reindex₁ f C ⟧ X (f i)           ↝⟨ ⟦reindex₁⟧↔ ext C ⟩□
  ⟦ C ⟧ (X ⊚ f) (f i)                □

-- An unfolding lemma for ⟦ reindex f C ⟧₂.

⟦reindex⟧₂↔ :
  ∀ {k ℓ x} {I O : Set ℓ} {X : Rel x O} →
  Extensionality? k ℓ ℓ →
  ∀ (C : Container I O) (f : I → O) (R : ∀ {o} → Rel₂ ℓ (X o)) {i}
  (x y : ⟦ reindex f C ⟧ X i) →

  ⟦ reindex f C ⟧₂ R (x , y)

    ↝[ k ]

  ⟦ C ⟧₂ R ( (proj₁ x , λ p → proj₂ x (_ , refl , p))
           , (proj₁ y , λ p → proj₂ y (_ , refl , p))
           )

⟦reindex⟧₂↔ ext C f R x y =

  ⟦ reindex f C ⟧₂ R (x , y)                           ↔⟨⟩

  ⟦ reindex₂ f (reindex₁ f C) ⟧₂ R (x , y)             ↔⟨⟩

  ⟦ reindex₁ f C ⟧₂ R (x , y)                          ↝⟨ ⟦reindex₁⟧₂↔ ext C f R x y ⟩□

  ⟦ C ⟧₂ R ( (proj₁ x , λ p → proj₂ x (_ , refl , p))
           , (proj₁ y , λ p → proj₂ y (_ , refl , p))
           )                                           □

-- If f is an involution, then ν (reindex f C) i is pointwise
-- logically equivalent to ν C i ⊚ f.

mutual

  ν-reindex⇔ :
    ∀ {ℓ} {I : Set ℓ} {C : Container I I} {f : I → I} →
    f ⊚ f ≡ P.id →
    ∀ {i x} → ν (reindex f C) i x ⇔ ν C i (f x)
  ν-reindex⇔ {C = C} {f} inv {i} {x} =
    ν (reindex f C) i x                     ↔⟨⟩
    ⟦ reindex f C ⟧ (ν′ (reindex f C) i) x  ↝⟨ ⟦reindex⟧↔ _ C ⟩
    ⟦ C ⟧ (ν′ (reindex f C) i ⊚ f) (f x)    ↝⟨ ⟦⟧-cong _ C (ν′-reindex⇔ inv) ⟩
    ⟦ C ⟧ (ν′ C i ⊚ f ⊚ f) (f x)            ↔⟨ ≡⇒↝ bijection $ cong (λ g → ⟦ C ⟧ (ν′ C i ⊚ g) (f x)) inv ⟩
    ⟦ C ⟧ (ν′ C i) (f x)                    ↔⟨⟩
    ν C i (f x)                             □

  ν′-reindex⇔ :
    ∀ {ℓ} {I : Set ℓ} {C : Container I I} {f : I → I} →
    f ⊚ f ≡ P.id →
    ∀ {i x} → ν′ (reindex f C) i x ⇔ ν′ C i (f x)
  ν′-reindex⇔ {C = C} {f} inv = record { to = to; from = from }
    where
    to : ∀ {i} → ν′ (reindex f C) i ⊆ ν′ C i ⊚ f
    force (to x) = _⇔_.to (ν-reindex⇔ inv) (force x)

    from : ∀ {i} → ν′ C i ⊚ f ⊆ ν′ (reindex f C) i
    force (from x) = _⇔_.from (ν-reindex⇔ inv) (force x)

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

-- An unfolding lemma for ⟦ C₁ ⊗ C₂ ⟧.

⟦⊗⟧↔ : ∀ {k ℓ x} {I O : Set ℓ} →
       Extensionality? k ℓ (ℓ ⊔ x) →
       ∀ (C₁ C₂ : Container I O) {X : Rel x I} {o} →
       ⟦ C₁ ⊗ C₂ ⟧ X o ↝[ k ] ⟦ C₁ ⟧ X o × ⟦ C₂ ⟧ X o
⟦⊗⟧↔ {k} {ℓ} ext C₁ C₂ {X} {o} =
  ⟦ C₁ ⊗ C₂ ⟧ X o                                                  ↔⟨⟩

  (∃ λ (s : Shape C₁ o × Shape C₂ o) →
   (λ i → Position C₁ (proj₁ s) i ⊎ Position C₂ (proj₂ s) i) ⊆ X)  ↔⟨ inverse Σ-assoc ⟩

  (∃ λ (s₁ : Shape C₁ o) →
   ∃ λ (s₂ : Shape C₂ o) →
   (λ i → Position C₁ s₁ i ⊎ Position C₂ s₂ i) ⊆ X)                ↝⟨ (∃-cong λ _ → ∃-cong λ _ → implicit-∀-cong ext $
                                                                       Π⊎↔Π×Π (lower-extensionality? k lzero ℓ ext)) ⟩
  (∃ λ (s₁ : Shape C₁ o) →
   ∃ λ (s₂ : Shape C₂ o) →
   ∀ {i} → (Position C₁ s₁ i → X i) × (Position C₂ s₂ i → X i))    ↔⟨ (∃-cong λ _ → ∃-cong λ _ → implicit-ΠΣ-comm) ⟩

  (∃ λ (s₁ : Shape C₁ o) →
   ∃ λ (s₂ : Shape C₂ o) →
   Position C₁ s₁ ⊆ X × Position C₂ s₂ ⊆ X)                        ↔⟨ (∃-cong λ _ → ∃-comm) ⟩

  (∃ λ (s₁ : Shape C₁ o) →
   Position C₁ s₁ ⊆ X
     ×
   ∃ λ (s₂ : Shape C₂ o) → Position C₂ s₂ ⊆ X)                     ↔⟨ Σ-assoc ⟩

  (∃ λ (s : Shape C₁ o) → Position C₁ s ⊆ X) ×
  (∃ λ (s : Shape C₂ o) → Position C₂ s ⊆ X)                       ↔⟨⟩

  ⟦ C₁ ⟧ X o × ⟦ C₂ ⟧ X o                                          □
  where
  open Container

-- An unfolding lemma for ⟦ C₁ ⊗ C₂ ⟧₂.

⟦⊗⟧₂↔ :
  ∀ {k ℓ x} {I : Set ℓ} {X : Rel x I} →
  Extensionality? k ℓ ℓ →
  ∀ (C₁ C₂ : Container I I) (R : ∀ {i} → Rel₂ ℓ (X i)) {i}
  (x y : ⟦ C₁ ⊗ C₂ ⟧ X i) →

  let (x₁ , x₂) , f = x
      (y₁ , y₂) , g = y
  in

  ⟦ C₁ ⊗ C₂ ⟧₂ R (x , y)

    ↝[ k ]

  ⟦ C₁ ⟧₂ R ((x₁ , f ⊚ inj₁) , (y₁ , g ⊚ inj₁))
    ×
  ⟦ C₂ ⟧₂ R ((x₂ , f ⊚ inj₂) , (y₂ , g ⊚ inj₂))

⟦⊗⟧₂↔ ext C₁ C₂ R (x@(x₁ , x₂) , f) (y@(y₁ , y₂) , g) =

  ⟦ C₁ ⊗ C₂ ⟧₂ R ((x , f) , (y , g))                                      ↔⟨⟩

  (∃ λ (eq : x ≡ y) →
   ∀ {o} (p : Position (C₁ ⊗ C₂) x o) →
   R (f p , g (subst (λ s → Position (C₁ ⊗ C₂) s o) eq p)))               ↔⟨⟩

  (∃ λ (eq : x ≡ y) →
   ∀ {o} (p : Position C₁ x₁ o ⊎ Position C₂ x₂ o) →
   R ( f p
     , g (subst (λ { (s₁ , s₂) → Position C₁ s₁ o ⊎ Position C₂ s₂ o })
                eq p)
     ))                                                                   ↔⟨ inverse (Σ-cong ≡×≡↔≡ λ _ → Bijection.id) ⟩

  (∃ λ (eq : x₁ ≡ y₁ × x₂ ≡ y₂) →
   ∀ {o} (p : Position C₁ x₁ o ⊎ Position C₂ x₂ o) →
   R ( f p
     , g (subst (λ { (s₁ , s₂) → Position C₁ s₁ o ⊎ Position C₂ s₂ o })
                (cong₂ _,_ (proj₁ eq) (proj₂ eq)) p)
     ))                                                                   ↔⟨ inverse Σ-assoc ⟩

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
                                                                              (∀-cong ext λ _ → ≡⇒↝ _ $ cong (R ⊚ (f _ ,_)) $
                                                                               lemma₁ eq₁ eq₂)
                                                                                ×-cong
                                                                              (∀-cong ext λ _ → ≡⇒↝ _ $ cong (R ⊚ (f _ ,_)) $
                                                                               lemma₂ eq₁ eq₂)) ⟩
  (∃ λ (eq₁ : x₁ ≡ y₁) →
   ∃ λ (eq₂ : x₂ ≡ y₂) →
   ∀ {o} →
   ((p : Position C₁ x₁ o) →
    R (f (inj₁ p) , g (inj₁ (subst (λ s₁ → Position C₁ s₁ o) eq₁ p))))
     ×
   ((p : Position C₂ x₂ o) →
    R (f (inj₂ p) , g (inj₂ (subst (λ s₂ → Position C₂ s₂ o) eq₂ p)))))   ↔⟨ (∃-cong λ _ → ∃-cong λ _ → implicit-ΠΣ-comm) ⟩

  (∃ λ (eq₁ : x₁ ≡ y₁) →
   ∃ λ (eq₂ : x₂ ≡ y₂) →
   (∀ {o} (p : Position C₁ x₁ o) →
    R (f (inj₁ p) , g (inj₁ (subst (λ s₁ → Position C₁ s₁ o) eq₁ p))))
     ×
   (∀ {o} (p : Position C₂ x₂ o) →
    R (f (inj₂ p) , g (inj₂ (subst (λ s₂ → Position C₂ s₂ o) eq₂ p)))))   ↔⟨ (∃-cong λ _ → ∃-comm) ⟩

  (∃ λ (eq₁ : x₁ ≡ y₁) →
   (∀ {o} (p : Position C₁ x₁ o) →
    R (f (inj₁ p) , g (inj₁ (subst (λ s₁ → Position C₁ s₁ o) eq₁ p))))
     ×
   ∃ λ (eq₂ : x₂ ≡ y₂) →
   (∀ {o} (p : Position C₂ x₂ o) →
    R (f (inj₂ p) , g (inj₂ (subst (λ s₂ → Position C₂ s₂ o) eq₂ p)))))   ↔⟨ Σ-assoc ⟩

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

  ⟦ C₁ ⟧₂ R ((x₁ , f ⊚ inj₁) , (y₁ , g ⊚ inj₁))
    ×
  ⟦ C₂ ⟧₂ R ((x₂ , f ⊚ inj₂) , (y₂ , g ⊚ inj₂))                           □

  where
  open Container

  lemma₁ = λ (eq₁ : x₁ ≡ y₁) (eq₂ : x₂ ≡ y₂) {o p} →

    g (subst (λ { (s₁ , s₂) → Position C₁ s₁ o ⊎ Position C₂ s₂ o })
             (cong₂ _,_ eq₁ eq₂) (inj₁ p))                            ≡⟨ cong g $ push-subst-inj₁ {y≡z = cong₂ _,_ eq₁ eq₂} _ _ ⟩

    g (inj₁ (subst (λ { (s₁ , s₂) → Position C₁ s₁ o })
                   (cong₂ _,_ eq₁ eq₂) p))                            ≡⟨ cong (g ⊚ inj₁) $ subst-∘ _ _ (cong₂ _,_ eq₁ eq₂) ⟩

    g (inj₁ (subst (λ s₁ → Position C₁ s₁ o)
                   (cong proj₁ (cong₂ _,_ eq₁ eq₂)) p))               ≡⟨ cong (g ⊚ inj₁) $ cong (flip (subst _) _) $ cong-proj₁-cong₂-, eq₁ eq₂ ⟩∎

    g (inj₁ (subst (λ s₁ → Position C₁ s₁ o) eq₁ p))                  ∎

  lemma₂ = λ (eq₁ : x₁ ≡ y₁) (eq₂ : x₂ ≡ y₂) {o p} →

    g (subst (λ { (s₁ , s₂) → Position C₁ s₁ o ⊎ Position C₂ s₂ o })
             (cong₂ _,_ eq₁ eq₂) (inj₂ p))                            ≡⟨ cong g $ push-subst-inj₂ {y≡z = cong₂ _,_ eq₁ eq₂} _ _ ⟩

    g (inj₂ (subst (λ { (s₁ , s₂) → Position C₂ s₂ o })
                   (cong₂ _,_ eq₁ eq₂) p))                            ≡⟨ cong (g ⊚ inj₂) $ subst-∘ _ _ (cong₂ _,_ eq₁ eq₂) ⟩

    g (inj₂ (subst (λ s₂ → Position C₂ s₂ o)
                   (cong proj₂ (cong₂ _,_ eq₁ eq₂)) p))               ≡⟨ cong (g ⊚ inj₂) $ cong (flip (subst _) _) $ cong-proj₂-cong₂-, eq₁ eq₂ ⟩∎

    g (inj₂ (subst (λ s₂ → Position C₂ s₂ o) eq₂ p))                  ∎

-- The greatest fixpoint ν (C₁ ⊗ C₂) i is contained in the
-- intersection ν C₁ i ∩ ν C₂ i.

ν-⊗⊆ :
  ∀ {ℓ} {I : Set ℓ} {C₁ C₂ : Container I I} {i} →
  ν (C₁ ⊗ C₂) i ⊆ ν C₁ i ∩ ν C₂ i
ν-⊗⊆ {C₁ = C₁} {C₂} {i} =
  ν (C₁ ⊗ C₂) i                                      ⊆⟨⟩
  ⟦ C₁ ⊗ C₂ ⟧ (ν′ (C₁ ⊗ C₂) i)                       ⊆⟨ ⟦⊗⟧↔ _ C₁ C₂ ⟩
  ⟦ C₁ ⟧ (ν′ (C₁ ⊗ C₂) i) ∩ ⟦ C₂ ⟧ (ν′ (C₁ ⊗ C₂) i)  ⊆⟨ Σ-map (map C₁ ν-⊗⊆₁′) (map C₂ ν-⊗⊆₂′) ⟩
  ⟦ C₁ ⟧ (ν′ C₁ i) ∩ ⟦ C₂ ⟧ (ν′ C₂ i)                ⊆⟨ P.id ⟩∎
  ν C₁ i ∩ ν C₂ i                                    ∎
  where
  ν-⊗⊆₁′ : ν′ (C₁ ⊗ C₂) i ⊆ ν′ C₁ i
  force (ν-⊗⊆₁′ x) = proj₁ (ν-⊗⊆ (force x))

  ν-⊗⊆₂′ : ν′ (C₁ ⊗ C₂) i ⊆ ν′ C₂ i
  force (ν-⊗⊆₂′ x) = proj₂ (ν-⊗⊆ (force x))

-- A disjoint union combinator.
--
-- Similar to a construction in "Containers: Constructing strictly
-- positive types" by Abbott, Altenkirch and Ghani (see
-- Proposition 3.5).

infixr 2 _⊕_

_⊕_ : ∀ {ℓ} {I O : Set ℓ} →
      Container I O → Container I O → Container I O
C₁ ⊕ C₂ =
  (λ o → Shape C₁ o ⊎ Shape C₂ o)
    ◁
  [ Position C₁ , Position C₂ ]
  where
  open Container

-- An unfolding lemma for ⟦ C₁ ⊕ C₂ ⟧.

⟦⊕⟧↔ : ∀ {ℓ x} {I O : Set ℓ}
       (C₁ C₂ : Container I O) {X : Rel x I} {o} →
       ⟦ C₁ ⊕ C₂ ⟧ X o ↔ ⟦ C₁ ⟧ X o ⊎ ⟦ C₂ ⟧ X o
⟦⊕⟧↔ C₁ C₂ {X} {o} =
  ⟦ C₁ ⊕ C₂ ⟧ X o                               ↔⟨⟩

  (∃ λ (s : Shape C₁ o ⊎ Shape C₂ o) →
   [ Position C₁ , Position C₂ ] s ⊆ X)         ↝⟨ ∃-⊎-distrib-right ⟩

  (∃ λ (s : Shape C₁ o) → Position C₁ s ⊆ X) ⊎
  (∃ λ (s : Shape C₂ o) → Position C₂ s ⊆ X)    ↔⟨⟩

  ⟦ C₁ ⟧ X o ⊎ ⟦ C₂ ⟧ X o                       □
  where
  open Container

-- An unfolding lemma for ⟦ C₁ ⊕ C₂ ⟧₂.

⟦⊕⟧₂↔ :
  ∀ {k ℓ x} {I : Set ℓ} {X : Rel x I} →
  Extensionality? k ℓ ℓ →
  ∀ (C₁ C₂ : Container I I) (R : ∀ {i} → Rel₂ ℓ (X i)) {i}
  (x y : ⟦ C₁ ⊕ C₂ ⟧ X i) →

  ⟦ C₁ ⊕ C₂ ⟧₂ R (x , y)

    ↝[ k ]

  (curry (⟦ C₁ ⟧₂ R) ⊎-rel curry (⟦ C₂ ⟧₂ R))
    (_↔_.to (⟦⊕⟧↔ C₁ C₂) x)
    (_↔_.to (⟦⊕⟧↔ C₁ C₂) y)

⟦⊕⟧₂↔ ext C₁ C₂ R (inj₁ x , f) (inj₁ y , g) =

  ⟦ C₁ ⊕ C₂ ⟧₂ R ((inj₁ x , f) , (inj₁ y , g))                   ↔⟨⟩

  (∃ λ (eq : inj₁ x ≡ inj₁ y) →
   ∀ {o} (p : Position C₁ x o) →
   R ( f p
     , g (subst (λ s → [_,_] {C = λ _ → Rel _ _}
                         (Position C₁) (Position C₂) s o) eq p)
     ))                                                          ↔⟨ inverse $ Σ-cong Bijection.≡↔inj₁≡inj₁ (λ _ → Bijection.id) ⟩

  (∃ λ (eq : x ≡ y) →
   ∀ {o} (p : Position C₁ x o) →
   R ( f p
     , g (subst (λ s → [_,_] {C = λ _ → Rel _ _}
                         (Position C₁) (Position C₂) s o)
                         (cong inj₁ eq) p)
     ))                                                          ↝⟨ (∃-cong λ eq → implicit-∀-cong ext $ ∀-cong ext λ _ →
                                                                     ≡⇒↝ _ $ cong (λ x → R (_ , g x)) $ sym $
                                                                     subst-∘ _ _ eq) ⟩
  (∃ λ (eq : x ≡ y) →
   ∀ {o} (p : Position C₁ x o) →
   R ( f p
     , g (subst (λ s → Position C₁ s o) eq p)
     ))                                                          ↔⟨⟩

  ⟦ C₁ ⟧₂ R ((x , f) , (y , g))                                  □

  where
  open Container

⟦⊕⟧₂↔ _ C₁ C₂ R (inj₁ x , f) (inj₂ y , g) =

  ⟦ C₁ ⊕ C₂ ⟧₂ R ((inj₁ x , f) , (inj₂ y , g))  ↔⟨⟩

  (∃ λ (eq : inj₁ x ≡ inj₂ y) → _)              ↔⟨ inverse $ Σ-cong (inverse Bijection.≡↔⊎) (λ _ → Bijection.id) ⟩

  (∃ λ (eq : ⊥) → _)                            ↔⟨ Σ-left-zero ⟩

  ⊥                                             □

⟦⊕⟧₂↔ _ C₁ C₂ R (inj₂ x , f) (inj₁ y , g) =

  ⟦ C₁ ⊕ C₂ ⟧₂ R ((inj₂ x , f) , (inj₁ y , g))  ↔⟨⟩

  (∃ λ (eq : inj₂ x ≡ inj₁ y) → _)              ↔⟨ inverse $ Σ-cong (inverse Bijection.≡↔⊎) (λ _ → Bijection.id) ⟩

  (∃ λ (eq : ⊥) → _)                            ↔⟨ Σ-left-zero ⟩

  ⊥                                             □

⟦⊕⟧₂↔ ext C₁ C₂ R (inj₂ x , f) (inj₂ y , g) =

  ⟦ C₁ ⊕ C₂ ⟧₂ R ((inj₂ x , f) , (inj₂ y , g))                   ↔⟨⟩

  (∃ λ (eq : inj₂ x ≡ inj₂ y) →
   ∀ {o} (p : Position C₂ x o) →
   R ( f p
     , g (subst (λ s → [_,_] {C = λ _ → Rel _ _}
                         (Position C₁) (Position C₂) s o) eq p)
     ))                                                          ↔⟨ inverse $ Σ-cong Bijection.≡↔inj₂≡inj₂ (λ _ → Bijection.id) ⟩

  (∃ λ (eq : x ≡ y) →
   ∀ {o} (p : Position C₂ x o) →
   R ( f p
     , g (subst (λ s → [_,_] {C = λ _ → Rel _ _}
                         (Position C₁) (Position C₂) s o)
                         (cong inj₂ eq) p)
     ))                                                          ↝⟨ (∃-cong λ eq → implicit-∀-cong ext $ ∀-cong ext λ _ →
                                                                     ≡⇒↝ _ $ cong (λ x → R (_ , g x)) $ sym $
                                                                     subst-∘ _ _ eq) ⟩
  (∃ λ (eq : x ≡ y) →
   ∀ {o} (p : Position C₂ x o) →
   R ( f p
     , g (subst (λ s → Position C₂ s o) eq p)
     ))                                                          ↔⟨⟩

  ⟦ C₂ ⟧₂ R ((x , f) , (y , g))                                  □

  where
  open Container

mutual

  -- A combinator that is similar to the function ⟷ from
  -- Section 6.3.4.1 in Pous and Sangiorgi's "Enhancements of the
  -- bisimulation proof method".

  ⟷[_] : ∀ {ℓ} {I : Set ℓ} →
         Container (I × I) (I × I) → Container (I × I) (I × I)
  ⟷[ C ] = C ⟷ C

  -- A generalisation of ⟷[_].

  infix 1 _⟷_

  _⟷_ : ∀ {ℓ} {I : Set ℓ} →
        (_ _ : Container (I × I) (I × I)) → Container (I × I) (I × I)
  C₁ ⟷ C₂ = C₁ ⊗ reindex swap C₂

-- An unfolding lemma for ⟦ C₁ ⟷ C₂ ⟧.

⟦⟷⟧↔ :
  ∀ {k ℓ x} {I : Set ℓ} →
  Extensionality? k ℓ (ℓ ⊔ x) →
  ∀ (C₁ C₂ : Container (I × I) (I × I)) {X : Rel₂ x I} {i} →
  ⟦ C₁ ⟷ C₂ ⟧ X i
    ↝[ k ]
  ⟦ C₁ ⟧ X i × ⟦ C₂ ⟧ (X ⊚ swap) (swap i)
⟦⟷⟧↔ ext C₁ C₂ {X} {i} =
  ⟦ C₁ ⟷ C₂ ⟧ X i                          ↔⟨⟩
  ⟦ C₁ ⊗ reindex swap C₂ ⟧ X i             ↝⟨ ⟦⊗⟧↔ ext C₁ (reindex swap C₂) ⟩
  ⟦ C₁ ⟧ X i × ⟦ reindex swap C₂ ⟧ X i     ↝⟨ ∃-cong (λ _ → ⟦reindex⟧↔ ext C₂) ⟩□
  ⟦ C₁ ⟧ X i × ⟦ C₂ ⟧ (X ⊚ swap) (swap i)  □

-- An unfolding lemma for ⟦ C₁ ⟷ C₂ ⟧₂.

⟦⟷⟧₂↔ :
  ∀ {k ℓ x} {I : Set ℓ} {X : Rel₂ x I} →
  Extensionality? k ℓ ℓ →
  ∀ (C₁ C₂ : Container (I × I) (I × I)) (R : ∀ {i} → Rel₂ ℓ (X i)) {i}
  (x y : ⟦ C₁ ⟷ C₂ ⟧ X i) →

  let (s₁ , s₂) , f = x
      (t₁ , t₂) , g = y
  in

  ⟦ C₁ ⟷ C₂ ⟧₂ R (x , y)

    ↝[ k ]

  ⟦ C₁ ⟧₂ R ((s₁ , f ⊚ inj₁) , (t₁ , g ⊚ inj₁))
    ×
  ⟦ C₂ ⟧₂ R ( (s₂ , λ p → f (inj₂ (_ , refl , p)))
            , (t₂ , λ p → g (inj₂ (_ , refl , p)))
            )

⟦⟷⟧₂↔ ext C₁ C₂ R x@((s₁ , s₂) , f) y@((t₁ , t₂) , g) =

  ⟦ C₁ ⟷ C₂ ⟧₂ R (x , y)                                      ↔⟨⟩

  ⟦ C₁ ⊗ reindex swap C₂ ⟧₂ R (x , y)                         ↝⟨ ⟦⊗⟧₂↔ ext C₁ (reindex swap C₂) R _ (_ , g) ⟩

  ⟦ C₁ ⟧₂ R ((s₁ , f ⊚ inj₁) , (t₁ , g ⊚ inj₁))
    ×
  ⟦ reindex swap C₂ ⟧₂ R ((s₂ , f ⊚ inj₂) , (t₂ , g ⊚ inj₂))  ↝⟨ ∃-cong (λ _ → ⟦reindex⟧₂↔ ext C₂ _ R _ (_ , g ⊚ inj₂)) ⟩□

  ⟦ C₁ ⟧₂ R ((s₁ , f ⊚ inj₁) , (t₁ , g ⊚ inj₁))
    ×
  ⟦ C₂ ⟧₂ R ( (s₂ , λ p → f (inj₂ (_ , refl , p)))
            , (t₂ , λ p → g (inj₂ (_ , refl , p)))
            )                                                 □

-- The following three lemmas correspond to the second part of
-- Exercise 6.3.24 in Pous and Sangiorgi's "Enhancements of the
-- bisimulation proof method".

-- Post-fixpoints of the container reindex₂ swap id ⊗ C are
-- post-fixpoints of ⟷[ C ].

⊆reindex₂-swap-⊗→⊆⟷ :
  ∀ {ℓ r} {I : Set ℓ} {C : Container (I × I) (I × I)} {R : Rel₂ r I} →
  R ⊆ ⟦ reindex₂ swap id ⊗ C ⟧ R → R ⊆ ⟦ ⟷[ C ] ⟧ R
⊆reindex₂-swap-⊗→⊆⟷ {C = C} {R} R⊆ =
  R                                  ⊆⟨ (λ x → lemma₁ x , lemma₂ x) ⟩
  ⟦ C ⟧ R ∩ R ⊚ swap                 ⊆⟨ Σ-map P.id lemma₃ ⟩
  ⟦ C ⟧ R ∩ ⟦ C ⟧ (R ⊚ swap) ⊚ swap  ⊆⟨ _⇔_.from (⟦⟷⟧↔ _ C C) ⟩∎
  ⟦ ⟷[ C ] ⟧ R                       ∎
  where
  lemma₀ =
    R                                 ⊆⟨ R⊆ ⟩
    ⟦ reindex₂ swap id ⊗ C ⟧ R        ⊆⟨ ⟦⊗⟧↔ _ (reindex₂ swap id) C ⟩∎
    ⟦ reindex₂ swap id ⟧ R ∩ ⟦ C ⟧ R  ∎

  lemma₁ =
    R                                 ⊆⟨ lemma₀ ⟩
    ⟦ reindex₂ swap id ⟧ R ∩ ⟦ C ⟧ R  ⊆⟨ proj₂ ⟩∎
    ⟦ C ⟧ R                           ∎

  lemma₂ =
    R                                 ⊆⟨ lemma₀ ⟩
    ⟦ reindex₂ swap id ⟧ R ∩ ⟦ C ⟧ R  ⊆⟨ proj₁ ⟩
    ⟦ reindex₂ swap id ⟧ R            ⊆⟨ P.id ⟩
    ⟦ id ⟧ R ⊚ swap                   ⊆⟨ _⇔_.to (⟦id⟧↔ _) ⟩∎
    R ⊚ swap                          ∎

  lemma₃ =
    R                 ⊆⟨ lemma₁ ⟩
    ⟦ C ⟧ R           ⊆⟨ map C lemma₂ ⟩∎
    ⟦ C ⟧ (R ⊚ swap)  ∎

-- The symmetric closure of a post-fixpoint of ⟷[ C ] is a
-- post-fixpoint of reindex₂ swap id ⊗ C.

⊆⟷→∪-swap⊆reindex₂-swap-⊗ :
  ∀ {ℓ r} {I : Set ℓ} {C : Container (I × I) (I × I)} {R : Rel₂ r I} →
  R ⊆ ⟦ ⟷[ C ] ⟧ R →
  R ∪ R ⊚ swap ⊆ ⟦ reindex₂ swap id ⊗ C ⟧ (R ∪ R ⊚ swap)
⊆⟷→∪-swap⊆reindex₂-swap-⊗ {C = C} {R} R⊆ =
  R ∪ R ⊚ swap                                                ⊆⟨ (λ x → lemma₁ x , lemma₂ x) ⟩
  ⟦ reindex₂ swap id ⟧ (R ∪ R ⊚ swap) ∩ ⟦ C ⟧ (R ∪ R ⊚ swap)  ⊆⟨ _⇔_.from (⟦⊗⟧↔ _ (reindex₂ swap id) C) ⟩∎
  ⟦ reindex₂ swap id ⊗ C ⟧ (R ∪ R ⊚ swap)                     ∎
  where
  lemma₁ =
    R ∪ R ⊚ swap                         ⊆⟨ [ inj₂ , inj₁ ] ⟩
    R ⊚ swap ∪ R                         ⊆⟨ P.id ⟩
    R ⊚ swap ∪ R ⊚ swap ⊚ swap           ⊆⟨ P.id ⟩
    (R ∪ R ⊚ swap) ⊚ swap                ⊆⟨ _⇔_.from (⟦id⟧↔ _) ⟩
    ⟦ id ⟧ (R ∪ R ⊚ swap) ⊚ swap         ⊆⟨ P.id ⟩∎
    ⟦ reindex₂ swap id ⟧ (R ∪ R ⊚ swap)  ∎

  lemma₂ =
    R ∪ R ⊚ swap                         ⊆⟨ ⊎-map R⊆ R⊆ ⟩

    ⟦ ⟷[ C ] ⟧ R ∪ ⟦ ⟷[ C ] ⟧ R ⊚ swap   ⊆⟨ ⊎-map (_⇔_.to (⟦⟷⟧↔ _ C C)) (_⇔_.to (⟦⟷⟧↔ _ C C)) ⟩

    ⟦ C ⟧ R ∩ ⟦ C ⟧ (R ⊚ swap) ⊚ swap ∪
    ⟦ C ⟧ R ⊚ swap ∩ ⟦ C ⟧ (R ⊚ swap)    ⊆⟨ ⊎-map proj₁ proj₂ ⟩

    ⟦ C ⟧ R ∪ ⟦ C ⟧ (R ⊚ swap)           ⊆⟨ [ map C inj₁ , map C inj₂ ] ⟩∎

    ⟦ C ⟧ (R ∪ R ⊚ swap)                 ∎

-- The greatest fixpoint of ⟷[ C ] is pointwise logically equivalent
-- to the greatest fixpoint of reindex₂ swap id ⊗ C.
--
-- Note that this proof is not necessarily size-preserving. TODO:
-- Figure out if the proof can be made size-preserving.

ν-⟷⇔ :
  ∀ {ℓ} {I : Set ℓ} {C : Container (I × I) (I × I)} {p} →
  ν ⟷[ C ] ∞ p ⇔ ν (reindex₂ swap id ⊗ C) ∞ p
ν-⟷⇔ {C = C} = record
  { to =
      let R = ν ⟷[ C ] ∞ in                                   $⟨ (λ {_} → ν-out) ⟩
      R ⊆ ⟦ ⟷[ C ] ⟧ R                                        ↝⟨ ⊆⟷→∪-swap⊆reindex₂-swap-⊗ ⟩
      R ∪ R ⊚ swap ⊆ ⟦ reindex₂ swap id ⊗ C ⟧ (R ∪ R ⊚ swap)  ↝⟨ unfold _ ⟩
      R ∪ R ⊚ swap ⊆ ν (reindex₂ swap id ⊗ C) ∞               ↝⟨ (λ hyp {_} x → hyp (inj₁ x)) ⟩□
      R ⊆ ν (reindex₂ swap id ⊗ C) ∞                          □

  ; from =
      let R = ν (reindex₂ swap id ⊗ C) ∞ in  $⟨ (λ {_} → ν-out) ⟩
      R ⊆ ⟦ reindex₂ swap id ⊗ C ⟧ R         ↝⟨ ⊆reindex₂-swap-⊗→⊆⟷ ⟩
      R ⊆ ⟦ ⟷[ C ] ⟧ R                       ↝⟨ unfold _ ⟩□
      R ⊆ ν ⟷[ C ] ∞                         □
  }
