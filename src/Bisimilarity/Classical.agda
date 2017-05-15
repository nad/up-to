------------------------------------------------------------------------
-- The classical definition of (strong) bisimilarity
------------------------------------------------------------------------

-- This module is largely based on "Enhancements of the bisimulation
-- proof method" by Pous and Sangiorgi.

{-# OPTIONS --without-K #-}

open import Labelled-transition-system

module Bisimilarity.Classical (lts : LTS) where

open import Equality.Propositional
open import Prelude

open LTS lts

open import Bisimilarity.Step lts _[_]⟶_ _[_]⟶_
open import Relation

------------------------------------------------------------------------
-- Progressions, bisimulations and bisimilarity

-- Progressions.

record Progression {r s}
                   (R : Rel₂ r Proc)
                   (S : Rel₂ s Proc) : Set (r ⊔ s) where
  field
    progression : R ⊆ Step S

  -- Some "projections".

  left-to-right :
    ∀ {p p′ q μ} →
    R (p , q) → p [ μ ]⟶ p′ → ∃ λ q′ → q [ μ ]⟶ q′ × S (p′ , q′)
  left-to-right pRq = Step.left-to-right (progression pRq)

  right-to-left :
    ∀ {p q q′ μ} →
    R (p , q) → q [ μ ]⟶ q′ → ∃ λ p′ → p [ μ ]⟶ p′ × S (p′ , q′)
  right-to-left pRq = Step.right-to-left (progression pRq)

open Progression public

-- A "constructor" for Progression.

⟪_,_⟫ :
  ∀ {r s} {R : Rel₂ r Proc} {S : Rel₂ s Proc} →
  (∀ {p p′ q μ} →
   R (p , q) → p [ μ ]⟶ p′ → ∃ λ q′ → q [ μ ]⟶ q′ × S (p′ , q′)) →
  (∀ {p q q′ μ} →
   R (p , q) → q [ μ ]⟶ q′ → ∃ λ p′ → p [ μ ]⟶ p′ × S (p′ , q′)) →
  Progression R S
Progression.progression ⟪ lr , rl ⟫ =
  λ pRq → ⟨ lr pRq , rl pRq ⟩

-- Bisimulations.

Bisimulation : ∀ {r} → Rel₂ r Proc → Set r
Bisimulation R = Progression R R

-- Bisimilarity.

Bisimilarity : ∀ ℓ → Rel₂ (lsuc ℓ) Proc
Bisimilarity ℓ pq =
  ∃ λ (R : Rel₂ ℓ Proc) → Bisimulation R × R pq

infix 4 [_]_∼_ _∼_

[_]_∼_ : ∀ ℓ → Proc → Proc → Set (lsuc ℓ)
[_]_∼_ ℓ = curry (Bisimilarity ℓ)

_∼_ : Proc → Proc → Set₁
p ∼ q = [ lzero ] p ∼ q

------------------------------------------------------------------------
-- Bisimilarity is an equivalence relation

-- Reflexivity.

reflexive-∼ : ∀ {ℓ p} → [ ℓ ] p ∼ p
reflexive-∼ {ℓ} =
    (λ { (p , q) → ↑ ℓ (p ≡ q) })
  , ⟪ (λ { (lift p≡q) p⟶p′ →
           _ , subst (_[ _ ]⟶ _) p≡q       p⟶p′ , lift refl })
    , (λ { (lift p≡q) q⟶q′ →
           _ , subst (_[ _ ]⟶ _) (sym p≡q) q⟶q′ , lift refl })
    ⟫
  , lift refl

-- Symmetry.

symmetric-∼ : ∀ {ℓ p q} → [ ℓ ] p ∼ q → [ ℓ ] q ∼ p
symmetric-∼ (R , R-is-a-bisimulation , pRq) =
    R ⁻¹
  , ⟪ right-to-left R-is-a-bisimulation
    , left-to-right R-is-a-bisimulation
    ⟫
  , pRq

-- Transitivity.

transitive-∼ : ∀ {ℓ p q r} → [ ℓ ] p ∼ q → [ ℓ ] q ∼ r → [ ℓ ] p ∼ r
transitive-∼ (R₁ , R-is₁ , pR₁q) (R₂ , R-is₂ , qR₂r) =
    R₁ ⊙ R₂
  , ⟪ (λ { (q , pR₁q , qR₂r) p⟶p′ →
           let q′ , q⟶q′ , p′R₁q′ = left-to-right R-is₁ pR₁q p⟶p′
               r′ , r⟶r′ , q′R₂r′ = left-to-right R-is₂ qR₂r q⟶q′
           in r′ , r⟶r′ , (q′ , p′R₁q′ , q′R₂r′) })
    , (λ { (q , pR₁q , qR₂r) r⟶r′ →
         let q′ , q⟶q′ , q′R₂r′ = right-to-left R-is₂ qR₂r r⟶r′
             p′ , p⟶p′ , p′R₁q′ = right-to-left R-is₁ pR₁q q⟶q′
         in p′ , p⟶p′ , (q′ , p′R₁q′ , q′R₂r′) })
    ⟫
  , _ , pR₁q , qR₂r

-- A function that can be used to aid the instance resolution
-- mechanism.

infix -2 ∼:_

∼:_ : ∀ {i p q} → [ i ] p ∼ q → [ i ] p ∼ q
∼:_ = id

------------------------------------------------------------------------
-- Lemmas relating bisimulations and bisimilarity

-- Bisimilarity is a bisimulation.

bisimilarity-is-a-bisimulation :
  ∀ {ℓ} → Bisimulation (Bisimilarity ℓ)
bisimilarity-is-a-bisimulation =
  ⟪ (λ { (_R_ , R-is-a-bisimulation , pRq) p⟶p′ →
         let q′ , q⟶q′ , p′Rq′ =
               left-to-right R-is-a-bisimulation pRq p⟶p′ in
           q′
         , q⟶q′
         , (_R_ , R-is-a-bisimulation , p′Rq′) })
  , (λ { (_R_ , R-is-a-bisimulation , pRq) q⟶q′ →
         let p′ , p⟶p′ , p′Rq′ =
               right-to-left R-is-a-bisimulation pRq q⟶q′ in
           p′
         , p⟶p′
         , (_R_ , R-is-a-bisimulation , p′Rq′) })
  ⟫

-- Bisimilarity is larger than every bisimulation.

bisimulation⊆∼ :
  ∀ {ℓ} {R : Rel₂ ℓ Proc} →
  Bisimulation R → R ⊆ Bisimilarity ℓ
bisimulation⊆∼ {R = R} R-is-a-bisimulation pRq =
  R , R-is-a-bisimulation , pRq

------------------------------------------------------------------------
-- Bisimulations up to bisimilarity

-- Bisimulations up to bisimilarity.

Bisimulation-up-to-bisimilarity :
  (ℓ : Level) → ∀ {r} → Rel₂ r Proc → Set (lsuc ℓ ⊔ r)
Bisimulation-up-to-bisimilarity ℓ R =
  Progression R (Bisimilarity ℓ ⊙ R ⊙ Bisimilarity ℓ)

-- If R is a bisimulation up to bisimilarity, then ∼R∼ is a
-- bisimulation.

bisimulation-up-to-∼⇒bisimulation :
  ∀ {ℓ r} {R : Rel₂ r Proc} →
  Bisimulation-up-to-bisimilarity ℓ R →
  Bisimulation (Bisimilarity ℓ ⊙ R ⊙ Bisimilarity ℓ)
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
  ∀ {ℓ r} {R : Rel₂ r Proc} →
  Bisimulation-up-to-bisimilarity ℓ R →
  R ⊆ Bisimilarity (lsuc ℓ ⊔ r)
bisimulation-up-to-∼⊆∼ {ℓ} {r} {R} R-is =
  R                                    ⊆⟨ (λ { {p , q} pRq → p , reflexive-∼ , q , pRq , reflexive-∼ }) ⟩
  Bisimilarity ℓ ⊙ R ⊙ Bisimilarity ℓ  ⊆⟨ bisimulation⊆∼ (bisimulation-up-to-∼⇒bisimulation R-is) ⟩∎
  Bisimilarity (lsuc ℓ ⊔ r)            ∎

------------------------------------------------------------------------
-- Bisimulations up to union

-- Bisimulations up to ∪.

Bisimulation-up-to-∪ :
  (ℓ : Level) → ∀ {r} → Rel₂ r Proc → Set (lsuc ℓ ⊔ r)
Bisimulation-up-to-∪ ℓ R =
  Progression R (R ∪ Bisimilarity ℓ)

-- If _R_ is a bisimulation up to ∪, then _R_ ∪ _∼_ is a bisimulation.

bisimulation-up-to-∪⇒bisimulation :
  ∀ {ℓ r} {R : Rel₂ r Proc} →
  Bisimulation-up-to-∪ ℓ R →
  Bisimulation (R ∪ Bisimilarity ℓ)
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
  ∀ {ℓ r} {R : Rel₂ r Proc} →
  Bisimulation-up-to-∪ ℓ R →
  R ⊆ Bisimilarity (lsuc ℓ ⊔ r)
bisimulation-up-to-∪⊆∼ {ℓ} {r} {R} R-is =
  R                          ⊆⟨ inj₁ ⟩
  R ∪ Bisimilarity ℓ         ⊆⟨ bisimulation⊆∼ (bisimulation-up-to-∪⇒bisimulation R-is) ⟩∎
  Bisimilarity (lsuc ℓ ⊔ r)  ∎

------------------------------------------------------------------------
-- Bisimulations up to reflexive transitive closure

-- Bisimulations up to reflexive transitive closure.

Bisimulation-up-to-* : Rel₂ (# 0) Proc → Set
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
  ∀ {R} → Bisimulation-up-to-* R → R ⊆ Bisimilarity (# 0)
bisimulation-up-to-*⊆∼ {R} R-is =
  R                   ⊆⟨ (λ pRq → 1 , _ , pRq , refl) ⟩
  (R *)               ⊆⟨ bisimulation⊆∼ (bisimulation-up-to-*⇒bisimulation R-is) ⟩∎
  Bisimilarity (# 0)  ∎

------------------------------------------------------------------------
-- Some preservation results

-- These results are not taken from "Enhancements of the bisimulation
-- proof method".

-- Equal processes are bisimilar.

≡⇒∼ : ∀ {ℓ p q} → p ≡ q → [ ℓ ] p ∼ q
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
  ∀ {ℓ} {R : Rel₂ ℓ Proc} →
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
