------------------------------------------------------------------------
-- Some results related to CCS, implemented without using a fixed form
-- of bisimilarity
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe --sized-types #-}

module Bisimilarity.CCS.General {ℓ} {Name : Set ℓ} where

open import Equality.Propositional
open import List equality-with-J
open import Prelude
open import Size

open import Labelled-transition-system
open import Labelled-transition-system.CCS Name

------------------------------------------------------------------------
-- Exercise 6.1.3 (1) from "Enhancements of the bisimulation proof
-- method" by Pous and Sangiorgi

6-1-3-1-proc : Proc ∞ → Proc ∞ → ℕ → Proc ∞
6-1-3-1-proc P P′ zero    = ! P ∣ P′
6-1-3-1-proc P P′ (suc n) = 6-1-3-1-proc P P′ n ∣ P

-- Note that the form of the expression is a bit more restrictive
-- than in the exercise formulation: (((! P | P′) | P)…) ∣ P.

6-1-3-1-without-τ :
  ∀ {a P P₀} → let μ = name a in
  ! P [ μ ]⟶ P₀ →
  ∃ λ P′ → ∃ λ n →
    P [ μ ]⟶ P′ × P₀ ≡ 6-1-3-1-proc P P′ n
6-1-3-1-without-τ {a} {P} (replication (par-right {Q′ = P′} tr)) =
    P′ , 0
  , (P   [ name a ]⟶⟨ tr ⟩
     P′)
  , (! P ∣ P′             ≡⟨ refl ⟩∎
     6-1-3-1-proc P P′ 0  ∎)
6-1-3-1-without-τ {a} {P} (replication (par-left {P′ = P′} tr)) =
  let P″ , n , tr′ , eq = 6-1-3-1-without-τ tr in

    P″ , suc n
  , (P   [ name a ]⟶⟨ tr′ ⟩
     P″)
  , (P′                  ∣ P    ≡⟨ cong (_∣ _) eq ⟩
     6-1-3-1-proc P P″ n ∣ P    ≡⟨ refl ⟩∎
     6-1-3-1-proc P P″ (suc n)  ∎)

One-step-away : {A : Set ℓ} → (A → Action) → Proc ∞ → Set ℓ
One-step-away f P = ∃ λ a → ∃ λ P′ → P [ f a ]⟶ P′

cons : {A B : Set ℓ} → A → List A × B → List A × B
cons x (xs , y) = x ∷ xs , y

6-1-3-1-proc′ :
  (P : Proc ∞) →
  List (Maybe (One-step-away name P)) × One-step-away id P →
  Proc ∞
6-1-3-1-proc′ P ([] , (_ , P′ , _))          = ! P ∣ P′
6-1-3-1-proc′ P (just (_ , P′ , _) ∷ Ps , o) = 6-1-3-1-proc′ P (Ps , o) ∣ P′
6-1-3-1-proc′ P (nothing           ∷ Ps , o) = 6-1-3-1-proc′ P (Ps , o) ∣ P

6-1-3-1-with-τ :
  ∀ {μ P P₀} →
  ! P [ μ ]⟶ P₀ →
  ∃ λ Ps → P₀ ≡ 6-1-3-1-proc′ P Ps
6-1-3-1-with-τ {μ} {P} (replication (par-right {Q′ = P′} tr)) =
    Ps
  , (! P ∣ P′            ≡⟨ refl ⟩∎
     6-1-3-1-proc′ P Ps  ∎)
  where
  Ps = [] , (μ , P′ , tr)

6-1-3-1-with-τ {μ} {P} (replication (par-left {P′ = P′} tr)) =
  let Ps , eq = 6-1-3-1-with-τ tr
      Ps′     = cons nothing Ps
  in
    Ps′
  , (P′ ∣ P                  ≡⟨ cong (_∣ _) eq ⟩
     6-1-3-1-proc′ P Ps ∣ P  ≡⟨ refl ⟩∎
     6-1-3-1-proc′ P Ps′     ∎)

6-1-3-1-with-τ .{τ} {P}
               (replication (par-τ {P′ = P′} {Q′ = Q′} {a = a}
                                   tr₁ tr₂)) =
  let Ps , eq = 6-1-3-1-with-τ tr₁
      Ps′     = cons (just (co a , Q′ , tr₂)) Ps
  in
    Ps′
  , (P′ ∣ Q′                  ≡⟨ cong (_∣ _) eq ⟩
     6-1-3-1-proc′ P Ps ∣ Q′  ≡⟨ refl ⟩∎
     6-1-3-1-proc′ P Ps′      ∎)

------------------------------------------------------------------------
-- Exercise 6.1.3 (2) from "Enhancements of the bisimulation proof
-- method" by Pous and Sangiorgi

-- Assumptions used to state and solve the exercise.

record 6-1-3-2-assumptions ℓ′ : Set (ℓ ⊔ lsuc ℓ′) where
  infix 4 _∼_
  infix  -1 finally-∼
  infixr -2 step-∼
  syntax finally-∼ p q p∼q = p ∼⟨ p∼q ⟩∎ q ∎
  syntax step-∼ p q∼r p∼q  = p ∼⟨ p∼q ⟩ q∼r

  field
    _∼_       : Proc ∞ → Proc ∞ → Set ℓ′
    step-∼    : ∀ P {Q R} → Q ∼ R → P ∼ Q → P ∼ R
    finally-∼ : ∀ P Q → P ∼ Q → P ∼ Q
    reflexive : ∀ {P} → P ∼ P
    symmetric : ∀ {P Q} → P ∼ Q → Q ∼ P
    ∣-comm    : ∀ {P Q} → P ∣ Q ∼ Q ∣ P
    ∣-assoc   : ∀ {P Q R} → P ∣ (Q ∣ R) ∼ (P ∣ Q) ∣ R
    _∣-cong_  : ∀ {P P′ Q Q′} → P ∼ P′ → Q ∼ Q′ → P ∣ Q ∼ P′ ∣ Q′
    6-1-2     : ∀ {P} → ! P ∣ P ∼ ! P

module 6-1-3-2 {ℓ′} (assumptions : 6-1-3-2-assumptions ℓ′) where

  open 6-1-3-2-assumptions assumptions

  swap-rightmost : ∀ {P Q R} → (P ∣ Q) ∣ R ∼ (P ∣ R) ∣ Q
  swap-rightmost {P} {Q} {R} =
    (P ∣ Q) ∣ R  ∼⟨ symmetric ∣-assoc ⟩
    P ∣ (Q ∣ R)  ∼⟨ reflexive ∣-cong ∣-comm ⟩
    P ∣ (R ∣ Q)  ∼⟨ ∣-assoc ⟩∎
    (P ∣ R) ∣ Q  ∎

  6-1-3-2 :
    ∀ {μ P P₀} →
    ! P [ μ ]⟶ P₀ →
    (∃ λ P′ → P [ μ ]⟶ P′ × P₀ ∼ ! P ∣ P′)
      ⊎
    (μ ≡ τ × ∃ λ P′ → ∃ λ P″ → ∃ λ a →
     P [ name a ]⟶ P′ × P [ name (co a) ]⟶ P″ × P₀ ∼ (! P ∣ P′) ∣ P″)
  6-1-3-2 {μ} {P} (replication (par-right {Q′ = P′} P⟶P′)) =
    inj₁ ( _
         , (P   [ μ ]⟶⟨ P⟶P′ ⟩
            P′)
         , (! P ∣ P′  ∼⟨ reflexive ⟩∎
            ! P ∣ P′  ∎))
  6-1-3-2 {μ} {P} (replication (par-left {P′ = P′} tr)) with 6-1-3-2 tr
  ... | inj₁ (P″ , P⟶P″ , P′∼!P∣P″) =
    inj₁ ( _
         , (P   [ μ ]⟶⟨ P⟶P″ ⟩
            P″)
         , (P′  ∣ P         ∼⟨ P′∼!P∣P″ ∣-cong reflexive ⟩
            (! P ∣ P″) ∣ P  ∼⟨ swap-rightmost ⟩
            (! P ∣ P) ∣ P″  ∼⟨ 6-1-2 ∣-cong reflexive ⟩∎
            ! P ∣ P″        ∎))
  ... | inj₂ (μ≡τ , P″ , P‴ , a , P⟶P″ , P⟶P‴ , P′∼!P∣P″∣P‴) =
    inj₂ ( μ≡τ , _ , _ , _
         , (P   [ name a ]⟶⟨ P⟶P″ ⟩
            P″)
         , (P   [ name (co a) ]⟶⟨ P⟶P‴ ⟩
            P‴)
         , (P′ ∣ P                 ∼⟨ P′∼!P∣P″∣P‴ ∣-cong reflexive ⟩
            ((! P ∣ P″) ∣ P‴) ∣ P  ∼⟨ swap-rightmost ⟩
            ((! P ∣ P″) ∣ P) ∣ P‴  ∼⟨ swap-rightmost ∣-cong reflexive ⟩
            ((! P ∣ P) ∣ P″) ∣ P‴  ∼⟨ (6-1-2 ∣-cong reflexive) ∣-cong reflexive ⟩∎
            (! P ∣ P″) ∣ P‴        ∎))
  6-1-3-2 {P = P} (replication (par-τ {P′ = P′} {Q′ = Q′} {a = a}
                                      tr P⟶Q′)) with 6-1-3-2 tr
  ... | inj₁ (P″ , P⟶P″ , P′∼!P∣P″) =
    inj₂ ( refl , _ , _ , _
         , (P   [ name a ]⟶⟨ P⟶P″ ⟩
            P″)
         , (P   [ name (co a) ]⟶⟨ P⟶Q′ ⟩
            Q′)
         , (P′ ∣ Q′          ∼⟨ P′∼!P∣P″ ∣-cong reflexive ⟩∎
            (! P ∣ P″) ∣ Q′  ∎))
  ... | inj₂ (() , _)
