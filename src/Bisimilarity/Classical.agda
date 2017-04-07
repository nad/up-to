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

open import Bisimilarity.Classical.Preliminaries

open LTS lts

------------------------------------------------------------------------
-- Progressions, bisimulations and bisimilarity

-- Progressions.

record Progression {r s}
  constructor ⟨_,_⟩
                   (_R_ : Rel r Proc)
                   (_S_ : Rel s Proc) : Set (r ⊔ s) where
  field
    left-to-right : ∀ {p p′ q μ} →
                    p R q → p [ μ ]⟶ p′ →
                    ∃ λ q′ → q [ μ ]⟶ q′ × p′ S q′
    right-to-left : ∀ {p q q′ μ} →
                    p R q → q [ μ ]⟶ q′ →
                    ∃ λ p′ → p [ μ ]⟶ p′ × p′ S q′

open Progression public

-- Bisimulations.

Bisimulation : ∀ {r} → Rel r Proc → Set r
Bisimulation _R_ = Progression _R_ _R_

-- Bisimilarity.

infix 4 [_]_∼_ _∼_

[_]_∼_ : ∀ ℓ → Rel (lsuc ℓ) Proc
[ ℓ ] p ∼ q =
  ∃ λ (_R_ : Rel ℓ Proc) → Bisimulation _R_ × p R q

_∼_ : Rel (# 1) Proc
p ∼ q = [ lzero ] p ∼ q

------------------------------------------------------------------------
-- Bisimilarity is an equivalence relation

-- Reflexivity.

reflexive-∼ : ∀ {ℓ p} → [ ℓ ] p ∼ p
reflexive-∼ =
    (λ p q → ↑ _ (p ≡ q))
  , ⟨ (λ { {q = ._} (lift refl) p⟶p′ → _ , p⟶p′ , lift refl })
    , (λ { {p = ._} (lift refl) q⟶q′ → _ , q⟶q′ , lift refl })
    ⟩
  , lift refl

-- Symmetry.

symmetric-∼ : ∀ {ℓ p q} → [ ℓ ] p ∼ q → [ ℓ ] q ∼ p
symmetric-∼ (_R_ , ⟨ left-to-right , right-to-left ⟩ , pRq) =
    flip _R_
  , ⟨ right-to-left
    , left-to-right
    ⟩
  , pRq

-- Transitivity.

transitive-∼ : ∀ {ℓ p q r} → [ ℓ ] p ∼ q → [ ℓ ] q ∼ r → [ ℓ ] p ∼ r
transitive-∼ (_R₁_ , ⟨ left-to-right₁ , right-to-left₁ ⟩ , pR₁q)
             (_R₂_ , ⟨ left-to-right₂ , right-to-left₂ ⟩ , qR₂r) =
    (λ p r → ∃ λ q → p R₁ q × q R₂ r)
  , ⟨ (λ { (q , pR₁q , qR₂r) p⟶p′ →
           let q′ , q⟶q′ , p′R₁q′ = left-to-right₁ pR₁q p⟶p′
               r′ , r⟶r′ , q′R₂r′ = left-to-right₂ qR₂r q⟶q′
           in r′ , r⟶r′ , (q′ , p′R₁q′ , q′R₂r′) })
    , (λ { (q′ , pR₁q , qR₂r) r⟶r′ →
         let q′ , q⟶q′ , q′R₂r′ = right-to-left₂ qR₂r r⟶r′
             p′ , p⟶p′ , p′R₁q′ = right-to-left₁ pR₁q q⟶q′
         in p′ , p⟶p′ , (q′ , p′R₁q′ , q′R₂r′) })
    ⟩
  , _ , pR₁q , qR₂r

-- A function that can be used to aid the instance resolution
-- mechanism.

infix -2 ∼:_

∼:_ : ∀ {i p q} → [ i ] p ∼ q → [ i ] p ∼ q
∼:_ = id

------------------------------------------------------------------------
-- Lemmas relating bisimulations and bisimilarity

-- Bisimilarity is a bisimulation.

bisimilarity-is-a-bisimulation : ∀ {ℓ} → Bisimulation [ ℓ ]_∼_
bisimilarity-is-a-bisimulation =
  ⟨ (λ { (_R_ , R-is-a-bisimulation , pRq) p⟶p′ →
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
  ⟩
  where
  open Progression

-- Bisimilarity is larger than every bisimulation.

bisimulation⊆∼ :
  ∀ {ℓ} {_R_ : Rel ℓ Proc} →
  Bisimulation _R_ → _R_ ⊆ [ ℓ ]_∼_
bisimulation⊆∼ {_R_ = _R_} R-is-a-bisimulation _ _ pRq =
  _R_ , R-is-a-bisimulation , pRq

------------------------------------------------------------------------
-- Bisimulations up to bisimilarity

-- Bisimulations up to bisimilarity.

Bisimulation-up-to-bisimilarity :
  (ℓ : Level) → ∀ {r} → Rel r Proc → Set (lsuc ℓ ⊔ r)
Bisimulation-up-to-bisimilarity ℓ _R_ =
  Progression _R_ ([ ℓ ]_∼_ ⊙ _R_ ⊙ [ ℓ ]_∼_)

-- If R is a bisimulation up to bisimilarity, then ∼R∼ is a
-- bisimulation.

bisimulation-up-to-∼⇒bisimulation :
  ∀ {ℓ r} {_R_ : Rel r Proc} →
  Bisimulation-up-to-bisimilarity ℓ _R_ →
  Bisimulation ([ ℓ ]_∼_ ⊙ _R_ ⊙ [ ℓ ]_∼_)
bisimulation-up-to-∼⇒bisimulation {ℓ} {_R_ = _R_} R-is =
  ⟨ (λ { (q , p∼q , r , qRr , r∼s) p⟶p′ →
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
  ⟩
  where
  open Progression

-- If R is a bisimulation up to bisimilarity, then R is contained in
-- bisimilarity.

bisimulation-up-to-∼⊆∼ :
  ∀ {ℓ r} {_R_ : Rel r Proc} →
  Bisimulation-up-to-bisimilarity ℓ _R_ →
  _R_ ⊆ [ lsuc ℓ ⊔ r ]_∼_
bisimulation-up-to-∼⊆∼ {ℓ} {r} {_R_} R-is =
  _R_                        ⊆⟨ (λ p q pRq → p , reflexive-∼ , q , pRq , reflexive-∼) ⟩
  [ ℓ ]_∼_ ⊙ _R_ ⊙ [ ℓ ]_∼_  ⊆⟨ bisimulation⊆∼ (bisimulation-up-to-∼⇒bisimulation R-is) ⟩∎
  [ lsuc ℓ ⊔ r ]_∼_          ∎

------------------------------------------------------------------------
-- Bisimulations up to union

-- Bisimulations up to ∪.

Bisimulation-up-to-∪ :
  (ℓ : Level) → ∀ {r} → (Proc → Proc → Set r) → Set (lsuc ℓ ⊔ r)
Bisimulation-up-to-∪ ℓ _R_ =
  Progression _R_ (_R_ ∪ [ ℓ ]_∼_)

-- If _R_ is a bisimulation up to ∪, then _R_ ∪ _∼_ is a bisimulation.

bisimulation-up-to-∪⇒bisimulation :
  ∀ {ℓ r} {_R_ : Rel r Proc} →
  Bisimulation-up-to-∪ ℓ _R_ →
  Bisimulation (_R_ ∪ [ ℓ ]_∼_)
bisimulation-up-to-∪⇒bisimulation {ℓ} {_R_ = _R_} R-is =
  ⟨ [ left-to-right R-is
    , (λ p∼q → Σ-map id (Σ-map id inj₂) ∘
               left-to-right bisimilarity-is-a-bisimulation p∼q)
    ]
  , [ right-to-left R-is
    , (λ p∼q → Σ-map id (Σ-map id inj₂) ∘
               right-to-left bisimilarity-is-a-bisimulation p∼q)
    ]
  ⟩
  where
  open Progression

-- If R is a bisimulation up to ∪, then R is contained in
-- bisimilarity.

bisimulation-up-to-∪⊆∼ :
  ∀ {ℓ r} {_R_ : Rel r Proc} →
  Bisimulation-up-to-∪ ℓ _R_ →
  _R_ ⊆ [ lsuc ℓ ⊔ r ]_∼_
bisimulation-up-to-∪⊆∼ {ℓ} {r} {_R_} R-is =
  _R_                ⊆⟨ (λ _ _ → inj₁) ⟩
  _R_ ∪ [ ℓ ]_∼_     ⊆⟨ bisimulation⊆∼ (bisimulation-up-to-∪⇒bisimulation R-is) ⟩∎
  [ lsuc ℓ ⊔ r ]_∼_  ∎

------------------------------------------------------------------------
-- Bisimulations up to reflexive transitive closure

-- Bisimulations up to reflexive transitive closure.

Bisimulation-up-to-* : Rel (# 0) Proc → Set
Bisimulation-up-to-* _R_ = Progression _R_ (_R_ *)

-- If _R_ is a bisimulation up to reflexive transitive closure, then
-- _R_ * is a bisimulation.

bisimulation-up-to-*⇒bisimulation :
  ∀ {_R_} → Bisimulation-up-to-* _R_ → Bisimulation (_R_ *)
bisimulation-up-to-*⇒bisimulation {_R_} R-is = ⟨ lr , rl ⟩
  where
  open Progression

  lr : ∀ {p p′ q μ} →
       (_R_ *) p q → p [ μ ]⟶ p′ →
       ∃ λ q′ → q [ μ ]⟶ q′ × (_R_ *) p′ q′
  lr (zero  , refl)           q⟶p′ = _ , q⟶p′ , zero , refl
  lr (suc n , r , pRr , rRⁿq) p⟶p′ =
    let r′ , r⟶r′ , p′R*r′ = left-to-right R-is pRr p⟶p′
        q′ , q⟶q′ , r′R*q′ = lr (n , rRⁿq) r⟶r′
    in q′ , q⟶q′ , *-trans p′R*r′ r′R*q′

  rl : ∀ {p q q′ μ} →
       (_R_ *) p q → q [ μ ]⟶ q′ →
       ∃ λ p′ → p [ μ ]⟶ p′ × (_R_ *) p′ q′
  rl (zero  , refl)           p⟶q′ = _ , p⟶q′ , zero , refl
  rl (suc n , r , pRr , rRⁿq) q⟶q′ =
    let r′ , r⟶r′ , r′R*q′ = rl (n , rRⁿq) q⟶q′
        p′ , p⟶p′ , p′R*r′ = right-to-left R-is pRr r⟶r′
    in p′ , p⟶p′ , *-trans p′R*r′ r′R*q′

-- If R is a bisimulation up to reflexive transitive closure, then R
-- is contained in bisimilarity.

bisimulation-up-to-*⊆∼ :
  ∀ {_R_} → Bisimulation-up-to-* _R_ → _R_ ⊆ _∼_
bisimulation-up-to-*⊆∼ {_R_} R-is =
  _R_      ⊆⟨ (λ _ _ pRq → 1 , _ , pRq , refl) ⟩
  (_R_ *)  ⊆⟨ bisimulation⊆∼ (bisimulation-up-to-*⇒bisimulation R-is) ⟩∎
  _∼_      ∎

------------------------------------------------------------------------
-- Some preservation results

-- These results are not taken from "Enhancements of the bisimulation
-- proof method".

-- Equal processes are bisimilar.

≡⇒∼ : ∀ {ℓ p q} → p ≡ q → [ ℓ ] p ∼ q
≡⇒∼ refl = reflexive-∼

-- The lifting operator preserves the "is a bisimulation" relation.

↑-preserves-bisimulations :
  ∀ {ℓ r} {_R_ : Rel r Proc} →
  Bisimulation _R_ → Bisimulation (λ p q → ↑ ℓ (p R q))
↑-preserves-bisimulations ⟨ left-to-right , right-to-left ⟩ =
  ⟨ (λ pRq → Σ-map id (Σ-map id lift) ∘ left-to-right (lower pRq))
  , (λ pRq → Σ-map id (Σ-map id lift) ∘ right-to-left (lower pRq))
  ⟩

-- The "times two" operator preserves the "is a bisimulation"
-- relation.

×2-preserves-bisimulations :
  ∀ {ℓ} {_R_ : Rel ℓ Proc} →
  Bisimulation _R_ →
  Bisimulation (λ p q → (p R q) ⊎ (p R q))
×2-preserves-bisimulations {_R_ = _R_} ⟨ lr , rl ⟩ =
  ⟨ (let f = λ pRq p⟶p′ → Σ-map id (Σ-map id inj₁) (lr pRq p⟶p′) in
     [ f , f ])
  , (let f = λ pRq q⟶q′ → Σ-map id (Σ-map id inj₁) (rl pRq q⟶q′) in
     [ f , f ])
  ⟩
