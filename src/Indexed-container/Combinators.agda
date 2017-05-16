------------------------------------------------------------------------
-- Container combinators
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Indexed-container.Combinators where

open import Equality.Propositional hiding (Extensionality)
open import Interval using (ext)
open import Prelude

open import Bijection equality-with-J as Bijection using (_↔_)
open import Function-universe equality-with-J as F hiding (_∘_)

open import Indexed-container
open import Relation

-- A reindexing combinator.
--
-- Taken from "Indexed containers" by Altenkirch, Ghani, Hancock,
-- McBride and Morris (JFP, 2015).

reindex₂ : ∀ {ℓ} {I O₁ O₂ : Set ℓ} →
           (O₂ → O₁) → Container I O₁ → Container I O₂
reindex₂ f C = C ∘ f

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

-- An unfolding lemma for ⟦ reindex₁ f C ⟧.

⟦reindex₁⟧↔ : ∀ {ℓ x} {I₁ I₂ O : Set ℓ} {f : I₁ → I₂}
              (C : Container I₁ O) {X : Rel x I₂} {o} →
              ⟦ reindex₁ f C ⟧ X o ↔ ⟦ C ⟧ (X ∘ f) o
⟦reindex₁⟧↔ {f = f} C {X} {o} =
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

-- An unfolding lemma for ⟦ C₁ ⊗ C₂ ⟧.

⟦⊗⟧↔ : ∀ {ℓ x} {I O : Set ℓ}
       (C₁ C₂ : Container I O) {X : Rel x I} {o} →
       ⟦ C₁ ⊗ C₂ ⟧ X o ↔ ⟦ C₁ ⟧ X o × ⟦ C₂ ⟧ X o
⟦⊗⟧↔ C₁ C₂ {X} {o} =
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
