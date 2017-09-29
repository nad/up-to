------------------------------------------------------------------------
-- The classical definition of (strong) bisimilarity
------------------------------------------------------------------------

-- This module is largely based on "Enhancements of the bisimulation
-- proof method" by Pous and Sangiorgi.

{-# OPTIONS --without-K #-}

open import Labelled-transition-system

module Bisimilarity.Classical {ℓ} (lts : LTS ℓ) where

open import Equality.Propositional
open import Logical-equivalence using (_⇔_)
open import Prelude

open import Function-universe equality-with-J hiding (id; _∘_)

open LTS lts

open import Bisimilarity.Step lts _[_]⟶_ _[_]⟶_ as S hiding (⟨_,_⟩)
open import Indexed-container
  hiding (⟨_⟩; Bisimilarity; larger⇔smallest)
open import Relation

------------------------------------------------------------------------
-- Progressions, bisimulations and bisimilarity

-- Progressions.

Progression : ∀ {r s} → Rel₂ r Proc → Rel₂ s Proc → Set (ℓ ⊔ r ⊔ s)
Progression R S = R ⊆ Step S

module Progression
        {r s} {R : Rel₂ r Proc} {S : Rel₂ s Proc}
        (P : Progression R S)
        where

  -- Some "projections".

  left-to-right :
    ∀ {p p′ q μ} →
    R (p , q) → p [ μ ]⟶ p′ → ∃ λ q′ → q [ μ ]⟶ q′ × S (p′ , q′)
  left-to-right pRq = Step.left-to-right (P pRq)

  right-to-left :
    ∀ {p q q′ μ} →
    R (p , q) → q [ μ ]⟶ q′ → ∃ λ p′ → p [ μ ]⟶ p′ × S (p′ , q′)
  right-to-left pRq = Step.right-to-left (P pRq)

open Progression public

-- A "constructor" for Progression.

⟪_,_⟫ :
  ∀ {r s} {R : Rel₂ r Proc} {S : Rel₂ s Proc} →
  (∀ {p p′ q μ} →
   R (p , q) → p [ μ ]⟶ p′ → ∃ λ q′ → q [ μ ]⟶ q′ × S (p′ , q′)) →
  (∀ {p q q′ μ} →
   R (p , q) → q [ μ ]⟶ q′ → ∃ λ p′ → p [ μ ]⟶ p′ × S (p′ , q′)) →
  Progression R S
⟪ lr , rl ⟫ = λ pRq → S.⟨ lr pRq , rl pRq ⟩

-- Bisimulations.

Bisimulation : ∀ {r} → Rel₂ r Proc → Set (ℓ ⊔ r)
Bisimulation R = Progression R R

-- Bisimilarity with a level argument.

Bisimilarity′ : ∀ ℓ′ → Rel₂ (lsuc (ℓ ⊔ ℓ′)) Proc
Bisimilarity′ ℓ′ = gfp ℓ′ S̲t̲e̲p̲

-- Bisimilarity′ ℓ′ is pointwise logically equivalent to
-- Bisimilarity′ lzero.
--
-- For this reason the code below is mostly restricted to
-- Bisimilarity′ lzero.

larger⇔smallest :
  ∀ ℓ′ {p} → Bisimilarity′ ℓ′ p ⇔ Bisimilarity′ lzero p
larger⇔smallest ℓ′ = Indexed-container.larger⇔smallest ℓ′

-- Bisimilarity.

Bisimilarity : Rel₂ (lsuc ℓ) Proc
Bisimilarity = Bisimilarity′ lzero

infix 4 _∼_

_∼_ : Proc → Proc → Set (lsuc ℓ)
_∼_ = curry Bisimilarity

-- An unfolding lemma for Bisimilarity′.

Bisimilarity′↔ :
  ∀ {k} ℓ′ {pq} →
  Extensionality? k (ℓ ⊔ ℓ′) (ℓ ⊔ ℓ′) →

  Bisimilarity′ ℓ′ pq
    ↝[ k ]
  ∃ λ (R : Rel₂ (ℓ ⊔ ℓ′) Proc) → Bisimulation R × R pq

Bisimilarity′↔ {k} ℓ′ {pq} ext =
  Bisimilarity′ ℓ′ pq                                     ↔⟨⟩
  gfp ℓ′ S̲t̲e̲p̲ pq                                          ↔⟨⟩
  (∃ λ (R : Rel₂ (ℓ ⊔ ℓ′) Proc) → R ⊆ ⟦ S̲t̲e̲p̲ ⟧ R × R pq)  ↝⟨ (∃-cong λ _ → ×-cong₁ λ _ → ⊆-congʳ ext $
                                                              inverse-ext? Step↔S̲t̲e̲p̲ (lower-extensionality? k ℓ′ lzero ext)) ⟩□
  (∃ λ (R : Rel₂ (ℓ ⊔ ℓ′) Proc) → Bisimulation R × R pq)  □

-- An unfolding lemma for Bisimilarity.

Bisimilarity↔ :
  ∀ {k pq} →
  Extensionality? k ℓ ℓ →

  Bisimilarity pq
    ↝[ k ]
  ∃ λ (R : Rel₂ ℓ Proc) → Bisimulation R × R pq

Bisimilarity↔ = Bisimilarity′↔ lzero

-- A "constructor".

⟨_,_,_⟩ :
  ∀ {p q} →
  (R : Rel₂ ℓ Proc) → Bisimulation R → R (p , q) → p ∼ q
⟨ R , bisim , pRq ⟩ = _⇔_.from (Bisimilarity↔ _) (R , bisim , pRq)

------------------------------------------------------------------------
-- Bisimilarity is an equivalence relation

-- Reflexivity, proved generally for Bisimilarity′.

reflexive-∼′ : ∀ ℓ {p} → Bisimilarity′ ℓ (p , p)
reflexive-∼′ ℓ = _⇔_.from (Bisimilarity′↔ ℓ _)
  ( ↑ ℓ ∘ uncurry _≡_
  ,  ⟪ (λ p≡q p⟶p′ →
          _ , subst (_[ _ ]⟶ _)       (lower p≡q) p⟶p′ , lift refl)
     , (λ p≡q q⟶q′ →
          _ , subst (_[ _ ]⟶ _) (sym $ lower p≡q) q⟶q′ , lift refl)
     ⟫
  , lift refl
  )

-- Reflexivity.

reflexive-∼ : ∀ {p} → p ∼ p
reflexive-∼ = reflexive-∼′ lzero

-- Symmetry.

symmetric-∼ : ∀ {p q} → p ∼ q → q ∼ p
symmetric-∼ p∼q with _⇔_.to (Bisimilarity↔ _) p∼q
... | R , R-is-a-bisimulation , pRq =
  ⟨ R ⁻¹
  , ⟪ right-to-left R-is-a-bisimulation
    , left-to-right R-is-a-bisimulation
    ⟫
  , pRq
  ⟩

-- Transitivity.

transitive-∼ : ∀ {p q r} → p ∼ q → q ∼ r → p ∼ r
transitive-∼ p∼q q∼r with _⇔_.to (Bisimilarity↔ _) p∼q
                        | _⇔_.to (Bisimilarity↔ _) q∼r
... | R₁ , R-is₁ , pR₁q | R₂ , R-is₂ , qR₂r =
  ⟨ R₁ ⊙ R₂
  , ⟪ (λ { (q , pR₁q , qR₂r) p⟶p′ →
           let q′ , q⟶q′ , p′R₁q′ = left-to-right R-is₁ pR₁q p⟶p′
               r′ , r⟶r′ , q′R₂r′ = left-to-right R-is₂ qR₂r q⟶q′
           in r′ , r⟶r′ , (q′ , p′R₁q′ , q′R₂r′) })
    , (λ { (q , pR₁q , qR₂r) r⟶r′ →
         let q′ , q⟶q′ , q′R₂r′ = right-to-left R-is₂ qR₂r r⟶r′
             p′ , p⟶p′ , p′R₁q′ = right-to-left R-is₁ pR₁q q⟶q′
         in p′ , p⟶p′ , (q′ , p′R₁q′ , q′R₂r′) })
    ⟫
  , (_ , pR₁q , qR₂r)
  ⟩

-- A function that can be used to aid the instance resolution
-- mechanism.

infix -2 ∼:_

∼:_ : ∀ {p q} → p ∼ q → p ∼ q
∼:_ = id

------------------------------------------------------------------------
-- Lemmas relating bisimulations and bisimilarity

-- Bisimilarity is a bisimulation.

bisimilarity-is-a-bisimulation : Bisimulation Bisimilarity
bisimilarity-is-a-bisimulation =
  Bisimilarity           ⊆⟨ gfp-out ℓ ⟩
  ⟦ S̲t̲e̲p̲ ⟧ Bisimilarity  ⊆⟨ _⇔_.from (Step↔S̲t̲e̲p̲ _) ⟩∎
  Step Bisimilarity      ∎

-- Bisimilarity is larger than every bisimulation.

bisimulation⊆∼ :
  ∀ {r} {R : Rel₂ r Proc} →
  Bisimulation R → R ⊆ Bisimilarity
bisimulation⊆∼ {r} {R} R-is-a-bisimulation =
  R                ⊆⟨ gfp-unfold lzero (

      R                 ⊆⟨ R-is-a-bisimulation ⟩
      Step R            ⊆⟨ Step↔S̲t̲e̲p̲ _ ⟩∎
      ⟦ S̲t̲e̲p̲ ⟧ R        ∎) ⟩

  Bisimilarity′ r  ⊆⟨ _⇔_.to (larger⇔smallest r) ⟩∎

  Bisimilarity     ∎

------------------------------------------------------------------------
-- Bisimulations up to bisimilarity

-- Bisimulations up to bisimilarity.

Bisimulation-up-to-bisimilarity :
  ∀ {r} → Rel₂ r Proc → Set (lsuc ℓ ⊔ r)
Bisimulation-up-to-bisimilarity R =
  Progression R (Bisimilarity ⊙ R ⊙ Bisimilarity)

-- If R is a bisimulation up to bisimilarity, then ∼R∼ is a
-- bisimulation.

bisimulation-up-to-∼⇒bisimulation :
  ∀ {r} {R : Rel₂ r Proc} →
  Bisimulation-up-to-bisimilarity R →
  Bisimulation (Bisimilarity ⊙ R ⊙ Bisimilarity)
bisimulation-up-to-∼⇒bisimulation R-is =
  ⟪ (λ { (q , p∼q , r , qRr , r∼s) p⟶p′ →
       let q′ , q⟶q′ , p′∼q′ =
             left-to-right bisimilarity-is-a-bisimulation p∼q p⟶p′
           r′ , r⟶r′ , (q″ , q′∼q″ , r″ , q″Rr″ , r″∼r′) =
             left-to-right R-is qRr q⟶q′
           s′ , s⟶s′ , r′∼s′ =
             left-to-right bisimilarity-is-a-bisimulation r∼s r⟶r′
       in
         s′ , s⟶s′ , q″
       , transitive-∼ p′∼q′ q′∼q″
       , r″ , q″Rr″
       , transitive-∼ r″∼r′ r′∼s′ })
  , (λ { (q , p∼q , r , qRr , r∼s) s⟶s′ →
       let r′ , r⟶r′ , r′∼s′ =
             right-to-left bisimilarity-is-a-bisimulation r∼s s⟶s′
           q′ , q⟶q′ , (q″ , q′∼q″ , r″ , q″Rr″ , r″∼r′) =
             right-to-left R-is qRr r⟶r′
           p′ , p⟶p′ , p′∼q′ =
             right-to-left bisimilarity-is-a-bisimulation p∼q q⟶q′
       in
         p′ , p⟶p′ , q″
       , transitive-∼ p′∼q′ q′∼q″
       , r″ , q″Rr″
       , transitive-∼ r″∼r′ r′∼s′ })
  ⟫

-- If R is a bisimulation up to bisimilarity, then R is contained in
-- bisimilarity.

bisimulation-up-to-∼⊆∼ :
  ∀ {r} {R : Rel₂ r Proc} →
  Bisimulation-up-to-bisimilarity R →
  R ⊆ Bisimilarity
bisimulation-up-to-∼⊆∼ {R = R} R-is =
  R                                ⊆⟨ (λ { {p , q} pRq → p , reflexive-∼ , q , pRq , reflexive-∼ }) ⟩
  Bisimilarity ⊙ R ⊙ Bisimilarity  ⊆⟨ bisimulation⊆∼ (bisimulation-up-to-∼⇒bisimulation R-is) ⟩∎
  Bisimilarity                     ∎

------------------------------------------------------------------------
-- Bisimulations up to union

-- Bisimulations up to ∪.

Bisimulation-up-to-∪ : ∀ {r} → Rel₂ r Proc → Set (lsuc ℓ ⊔ r)
Bisimulation-up-to-∪ R = Progression R (R ∪ Bisimilarity)

-- If _R_ is a bisimulation up to ∪, then _R_ ∪ _∼_ is a bisimulation.

bisimulation-up-to-∪⇒bisimulation :
  ∀ {r} {R : Rel₂ r Proc} →
  Bisimulation-up-to-∪ R →
  Bisimulation (R ∪ Bisimilarity)
bisimulation-up-to-∪⇒bisimulation R-is =
  ⟪ [ left-to-right R-is
    , (λ p∼q → Σ-map id (Σ-map id inj₂) ∘
               left-to-right bisimilarity-is-a-bisimulation p∼q)
    ]
  , [ right-to-left R-is
    , (λ p∼q → Σ-map id (Σ-map id inj₂) ∘
               right-to-left bisimilarity-is-a-bisimulation p∼q)
    ]
  ⟫

-- If R is a bisimulation up to ∪, then R is contained in
-- bisimilarity.

bisimulation-up-to-∪⊆∼ :
  ∀ {r} {R : Rel₂ r Proc} →
  Bisimulation-up-to-∪ R →
  R ⊆ Bisimilarity
bisimulation-up-to-∪⊆∼ {R = R} R-is =
  R                 ⊆⟨ inj₁ ⟩
  R ∪ Bisimilarity  ⊆⟨ bisimulation⊆∼ (bisimulation-up-to-∪⇒bisimulation R-is) ⟩∎
  Bisimilarity      ∎

------------------------------------------------------------------------
-- Bisimulations up to reflexive transitive closure

-- Bisimulations up to reflexive transitive closure.

Bisimulation-up-to-* : Rel₂ ℓ Proc → Set ℓ
Bisimulation-up-to-* R = Progression R (R *)

-- If R is a bisimulation up to reflexive transitive closure, then R *
-- is a bisimulation.

bisimulation-up-to-*⇒bisimulation :
  ∀ {R} → Bisimulation-up-to-* R → Bisimulation (R *)
bisimulation-up-to-*⇒bisimulation {R} R-is = ⟪ lr , rl ⟫
  where
  lr : ∀ {p p′ q μ} →
       (R *) (p , q) → p [ μ ]⟶ p′ →
       ∃ λ q′ → q [ μ ]⟶ q′ × (R *) (p′ , q′)
  lr (zero  , refl)           q⟶p′ = _ , q⟶p′ , zero , refl
  lr (suc n , r , pRr , rRⁿq) p⟶p′ =
    let r′ , r⟶r′ , p′R*r′ = left-to-right R-is pRr p⟶p′
        q′ , q⟶q′ , r′R*q′ = lr (n , rRⁿq) r⟶r′
    in q′ , q⟶q′ , *-trans p′R*r′ r′R*q′

  rl : ∀ {p q q′ μ} →
       (R *) (p , q) → q [ μ ]⟶ q′ →
       ∃ λ p′ → p [ μ ]⟶ p′ × (R *) (p′ , q′)
  rl (zero  , refl)           p⟶q′ = _ , p⟶q′ , zero , refl
  rl (suc n , r , pRr , rRⁿq) q⟶q′ =
    let r′ , r⟶r′ , r′R*q′ = rl (n , rRⁿq) q⟶q′
        p′ , p⟶p′ , p′R*r′ = right-to-left R-is pRr r⟶r′
    in p′ , p⟶p′ , *-trans p′R*r′ r′R*q′

-- If R is a bisimulation up to reflexive transitive closure, then R
-- is contained in bisimilarity.

bisimulation-up-to-*⊆∼ :
  ∀ {R} → Bisimulation-up-to-* R → R ⊆ Bisimilarity
bisimulation-up-to-*⊆∼ {R} R-is =
  R             ⊆⟨ (λ pRq → 1 , _ , pRq , refl) ⟩
  (R *)         ⊆⟨ bisimulation⊆∼ (bisimulation-up-to-*⇒bisimulation R-is) ⟩∎
  Bisimilarity  ∎

------------------------------------------------------------------------
-- Some preservation results

-- These results are not taken from "Enhancements of the bisimulation
-- proof method".

-- Equal processes are bisimilar.

≡⇒∼ : ∀ {p q} → p ≡ q → p ∼ q
≡⇒∼ refl = reflexive-∼

-- Precomposition with the lifting operator preserves the "is a
-- bisimulation" relation.

↑-preserves-bisimulations :
  ∀ {ℓ r} {R : Rel₂ r Proc} →
  Bisimulation R → Bisimulation (↑ ℓ ∘ R)
↑-preserves-bisimulations R-is =
  ⟪ (λ pRq → Σ-map id (Σ-map id lift) ∘ left-to-right R-is (lower pRq))
  , (λ pRq → Σ-map id (Σ-map id lift) ∘ right-to-left R-is (lower pRq))
  ⟫

-- The "times two" operator preserves the "is a bisimulation"
-- relation.

×2-preserves-bisimulations :
  ∀ {r} {R : Rel₂ r Proc} →
  Bisimulation R →
  Bisimulation (R ∪ R)
×2-preserves-bisimulations R-is =
  ⟪ (let f = λ pRq p⟶p′ →
               Σ-map id (Σ-map id inj₁) (left-to-right R-is pRq p⟶p′) in
     [ f , f ])
  , (let f = λ pRq q⟶q′ →
               Σ-map id (Σ-map id inj₁) (right-to-left R-is pRq q⟶q′) in
     [ f , f ])
  ⟫
