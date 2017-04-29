------------------------------------------------------------------------
-- Up-to techniques
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

open import Labelled-transition-system

module Bisimilarity.Up-to (lts : LTS) where

open import Equality.Propositional
open import Logical-equivalence using (_⇔_)
open import Prelude

open import Bijection equality-with-J using (_↔_)
open import Function-universe equality-with-J as F hiding (id; _∘_)

open LTS lts

import Bisimilarity.Classical
open import Bisimilarity.Classical.Preliminaries
import Bisimilarity.Coinductive
import Bisimilarity.Coinductive.Equational-reasoning-instances
open import Bisimilarity.Comparison
open import Bisimilarity.Step lts _[_]⟶_
open import Equational-reasoning
open import Indexed-container

private
  module Cl = Bisimilarity.Classical   lts
  module Co = Bisimilarity.Coinductive lts

------------------------------------------------------------------------
-- General results

-- A relation transformer F is an up-to technique if every relation
-- R that progresses to F R is contained in bisimilarity.
--
-- This is roughly what Pous and Sangiorgi refer to as "enhancement
-- of the bisimulation proof method" in "Enhancements of the
-- bisimulation proof method", with the main difference that they
-- require R to be contained in F R.

Up-to-technique : ∀ {ℓ} → Trans ℓ Proc → Set (lsuc ℓ)
Up-to-technique {ℓ} F =
  (R : Rel ℓ Proc) →
  Cl.Progression R (F R) → R ⊆ Co._∼_

-- Step-compatibility.
--
-- This definition corresponds to Pous and Sangiorgi's definition of
-- b-compatibility, specialised to bisimilarity.

Step-compatible : ∀ {ℓ} → Trans ℓ Proc → Set (lsuc ℓ)
Step-compatible F = ∀ R → F (⟦ S̲t̲e̲p̲ ⟧₂ R) ⊆ ⟦ S̲t̲e̲p̲ ⟧₂ (F R)

-- Monotone step-compatible functions are up-to techniques.
--
-- This is basically Pous and Sangiorgi's Theorem 6.3.9, specialised
-- to bisimilarity. Note that the proof does not depend on any details
-- of Step, except for the fact that it is monotone.

module _
  {ℓ}
  (F    : Trans ℓ Proc)
  (mono : Monotone F)
  (comp : Step-compatible F)
  where

  private

    -- Repeated composition of a function with itself.

    infix 10 _^[_]_

    _^[_]_ : ∀ {a} {A : Set a} → (A → A) → ℕ → A → A
    f ^[ zero  ] x = x
    f ^[ suc n ] x = f (f ^[ n ] x)

    module _ (R : Rel ℓ Proc) (R-prog : Cl.Progression R (F R)) where

      -- A lemma.

      Fⁿ⊆Step∘F¹⁺ⁿ : ∀ n → F ^[ n ] R ⊆ ⟦ S̲t̲e̲p̲ ⟧₂ (F ^[ suc n ] R)
      Fⁿ⊆Step∘F¹⁺ⁿ zero =
        R                ⊆⟨ Cl.progression R-prog ⟩
        Step (F R)       ⊆⟨ (λ _ _ → _↔_.to Step↔S̲t̲e̲p̲) ⟩∎
        ⟦ S̲t̲e̲p̲ ⟧₂ (F R)  ∎
      Fⁿ⊆Step∘F¹⁺ⁿ (suc n) =
        F ^[ 1 + n ] R                  ⊆⟨⟩
        F (F ^[ n ] R)                  ⊆⟨ mono (Fⁿ⊆Step∘F¹⁺ⁿ n) ⟩
        F (⟦ S̲t̲e̲p̲ ⟧₂ (F ^[ 1 + n ] R))  ⊆⟨ comp _ ⟩∎
        ⟦ S̲t̲e̲p̲ ⟧₂ (F ^[ 2 + n ] R)      ∎

      -- An analogue of ⋃ₙ Fⁿ(R).

      F^ωR : Rel ℓ Proc
      F^ωR p q = ∃ λ n → (F ^[ n ] R) p q

      -- F^ωR is a bisimulation.

      F^ωR-bisim : Cl.Bisimulation F^ωR
      Cl.progression F^ωR-bisim p q = uncurry λ n →
        (F ^[ n ] R                  ⊆⟨ Fⁿ⊆Step∘F¹⁺ⁿ n ⟩
         ⟦ S̲t̲e̲p̲ ⟧₂ (F ^[ 1 + n ] R)  ⊆⟨ S̲t̲e̲p̲-monotone (λ _ _ → 1 + n ,_) ⟩
         ⟦ S̲t̲e̲p̲ ⟧₂ F^ωR              ⊆⟨ (λ _ _ → _↔_.from Step↔S̲t̲e̲p̲) ⟩∎
         Step F^ωR                   ∎) p q

  compatible→up-to : Up-to-technique F
  compatible→up-to R R-prog =
    R              ⊆⟨ (λ _ _ → 0 ,_) ⟩
    F^ωR R R-prog  ⊆⟨ Cl.bisimulation⊆∼ (F^ωR-bisim R R-prog) ⟩
    Cl.[ ℓ ]_∼_    ⊆⟨ (λ _ _ → cl⇒co) ⟩∎
    Co._∼_         ∎

-- F is "bisimilarity-size-preserving" if, for any relation R, if R
-- is contained in bisimilarity /of size i/, then F R is contained
-- in bisimilarity of size i.

Bisimilarity-size-preserving :
  ∀ {ℓ} → Trans ℓ Proc → Set (lsuc ℓ)
Bisimilarity-size-preserving {ℓ} F =
  ∀ {R : Rel ℓ Proc} {i} →
  R ⊆ Co.[ i ]_∼_ → F R ⊆ Co.[ i ]_∼_

-- If the relation transformer F is bisimilarity-size-preserving,
-- then F is an up-to technique.
--
-- On the other hand, up-to techniques are not necessarily
-- bisimilarity-size-preserving, not even for monotone transformers,
-- see
-- Bisimilarity.Up-to.Counterexamples.¬monotone→up-to→size-preserving.
-- Thus the property of being bisimilarity-size-preserving is less
-- general than that of being an up-to technique. However, the latter
-- property is not closed under composition (not even for monotone
-- transformers, see Bisimilarity.Up-to.Counterexamples.¬-∘-closure),
-- whereas the former property is (see ∘-closure below).

module _
  {ℓ}
  (F    : Trans ℓ Proc)
  (pres : Bisimilarity-size-preserving F)
  where

  private

    -- F is also bisimilarity-size-preserving for the primed variant
    -- of bisimilarity.

    pres′ : ∀ {R : Rel ℓ Proc} {i} →
            R ⊆ Co.[ i ]_∼′_ → F R ⊆ Co.[ i ]_∼′_
    force (pres′ R⊆∼′ p q FRpq) =
      pres (λ p′ q′ Rp′q′ → force (R⊆∼′ p′ q′ Rp′q′)) p q FRpq

    size-preserving→up-to′ :
      ∀ {i} (R : Rel ℓ Proc) →
      Cl.Progression R (F R) → R ⊆ Co.[ i ]_∼_
    size-preserving→up-to′ {i} R prog p q Rpq =
      S̲t̲e̲p̲.⟨ (λ {p′ μ} →
                p [ μ ]⟶ p′                                 ↝⟨ Cl.left-to-right prog Rpq ⟩
                (∃ λ q′ → q [ μ ]⟶ q′ × F R p′ q′)          ↝⟨ Σ-map id (Σ-map id (pres′ size-preserving→up-to″ _ _)) ⟩□
                (∃ λ q′ → q [ μ ]⟶ q′ × Co.[ i ] p′ ∼′ q′)  □)
           , (λ {q′ μ} →
                q [ μ ]⟶ q′                                 ↝⟨ Cl.right-to-left prog Rpq ⟩
                (∃ λ p′ → p [ μ ]⟶ p′ × F R p′ q′)          ↝⟨ Σ-map id (Σ-map id (pres′ size-preserving→up-to″ _ _)) ⟩□
                (∃ λ p′ → p [ μ ]⟶ p′ × Co.[ i ] p′ ∼′ q′)  □)
           ⟩
      where
      size-preserving→up-to″ : R ⊆ Co.[ i ]_∼′_
      force (size-preserving→up-to″ p q Rpq) =
        size-preserving→up-to′ R prog p q Rpq

  size-preserving→up-to : Up-to-technique F
  size-preserving→up-to = size-preserving→up-to′

-- If F is monotone, then Bisimilarity-size-preserving F is logically
-- equivalent to a special case stating that, for any size i,
-- Co.[ i ]_∼_ should be a pre-fixpoint of F (modulo a lifting).
--
-- Note that bisimilarity-size-preserving relation transformers are
-- not necessarily monotone, see
-- Bisimilarity.Up-to.Counterexamples.¬size-preserving→monotone.

monotone→⇔ :
  ∀ {ℓ} (F : Trans ℓ Proc) →
  Monotone F →
  Bisimilarity-size-preserving F
    ⇔
  (∀ {i} → F ([ ↑ ℓ ]⊙ Co.[ i ]_∼_) ⊆ Co.[ i ]_∼_)
monotone→⇔ {ℓ} F F-mono = record
  { to   = λ pres {i} →
             F ([ ↑ ℓ ]⊙ Co.[ i ]_∼_)  ⊆⟨ pres (λ _ _ → lower) ⟩∎
             Co.[ i ]_∼_               ∎
  ; from = λ drop {R i} R⊆∼ →
             F R                       ⊆⟨ F-mono (

                 R                          ⊆⟨ R⊆∼ ⟩
                 Co.[ i ]_∼_                ⊆⟨ (λ _ _ → lift) ⟩∎
                 [ ↑ ℓ ]⊙ Co.[ i ]_∼_       ∎) ⟩

             F ([ ↑ ℓ ]⊙ Co.[ i ]_∼_)  ⊆⟨ drop ⟩∎

             Co.[ i ]_∼_               ∎
  }

-- The lifting used in the statement of monotone→⇔ can be omitted if F
-- transforms relations targeting Set₀.

monotone→⇔₀ :
  (F : Trans (# 0) Proc) →
  Monotone F →
  Bisimilarity-size-preserving F
    ⇔
  (∀ {i} → F Co.[ i ]_∼_ ⊆ Co.[ i ]_∼_)
monotone→⇔₀ F F-mono =
  Bisimilarity-size-preserving F                        ↝⟨ monotone→⇔ F F-mono ⟩
  (∀ {i} → F ([ ↑ lzero ]⊙ Co.[ i ]_∼_) ⊆ Co.[ i ]_∼_)  ↝⟨ implicit-∀-cong-⇔ (∀-cong-⇔ λ _ → ∀-cong-⇔ λ _ → →-cong-⇔
                                                             (record { to   = F-mono (λ _ _ → lower) _ _
                                                                     ; from = F-mono (λ _ _ → lift)  _ _
                                                                     })
                                                             F.id) ⟩□
  (∀ {i} → F Co.[ i ]_∼_ ⊆ Co.[ i ]_∼_)                 □

-- The lifting used in the statement of monotone→⇔ can be omitted if F
-- is universe-polymorphic in a certain sense, and the monotonicity
-- property is also universe-polymorphic.

monotone→⇔∀ :
  ∀ {ℓ} (F : ∀ {ℓ} → Trans ℓ Proc) →
  (∀ {r s} → Monotone-∀ F r s) →
  Bisimilarity-size-preserving {ℓ = ℓ} F
    ⇔
  (∀ {i} → F Co.[ i ]_∼_ ⊆ Co.[ i ]_∼_)
monotone→⇔∀ {ℓ} F F-mono =
  Bisimilarity-size-preserving F                    ↝⟨ monotone→⇔ F F-mono ⟩
  (∀ {i} → F ([ ↑ ℓ ]⊙ Co.[ i ]_∼_) ⊆ Co.[ i ]_∼_)  ↝⟨ implicit-∀-cong-⇔ (∀-cong-⇔ λ _ → ∀-cong-⇔ λ _ → →-cong-⇔
                                                         (record { to   = F-mono (λ _ _ → lower) _ _
                                                                 ; from = F-mono (λ _ _ → lift)  _ _
                                                                 })
                                                         F.id) ⟩□
  (∀ {i} → F Co.[ i ]_∼_ ⊆ Co.[ i ]_∼_)             □

-- A corollary of size-preserving→up-to and monotone→⇔₀.

size-preserving→up-to₀ :
  (F : Trans (# 0) Proc) →
  Monotone F →
  (∀ {i} → F Co.[ i ]_∼_ ⊆ Co.[ i ]_∼_) →
  Up-to-technique F
size-preserving→up-to₀ F mono =
  (∀ {i} → F Co.[ i ]_∼_ ⊆ Co.[ i ]_∼_)  ↝⟨ _⇔_.from (monotone→⇔₀ F mono) ⟩
  Bisimilarity-size-preserving F         ↝⟨ size-preserving→up-to F ⟩□
  Up-to-technique F                      □

-- A corollary of size-preserving→up-to and monotone→⇔∀.

size-preserving→up-to-∀ :
  ∀ {ℓ} (F : ∀ {ℓ} → Trans ℓ Proc) →
  (∀ {r s} → Monotone-∀ F r s) →
  (∀ {i} → F Co.[ i ]_∼_ ⊆ Co.[ i ]_∼_) →
  Up-to-technique {ℓ = ℓ} F
size-preserving→up-to-∀ F mono =
  (∀ {i} → F Co.[ i ]_∼_ ⊆ Co.[ i ]_∼_)  ↝⟨ _⇔_.from (monotone→⇔∀ F mono) ⟩
  Bisimilarity-size-preserving F         ↝⟨ size-preserving→up-to F ⟩□
  Up-to-technique F                      □

-- Monotone, step-compatible transformers are
-- bisimilarity-size-preserving.
--
-- On the other hand bisimilarity-size-preserving transformers are not
-- necessarily step-compatible, not even if they are monotone, see
-- Bisimilarity.Up-to.Counterexample.¬monotone→size-preserving→compatible.
-- Thus the property of being bisimilarity-size-preserving is more
-- general than the property of being step-compatible. However, it is
-- more well-behaved than Up-to-technique, because it is closed under
-- composition (see below).

monotone→compatible→size-preserving :
  ∀ {ℓ} (F : Trans ℓ Proc) →
  Monotone F →
  Step-compatible F →
  Bisimilarity-size-preserving F
monotone→compatible→size-preserving {ℓ} F mono comp =
  _⇔_.from (monotone→⇔ F mono) lemma
  where

  mutual

    lemma : ∀ {i} → F ([ ↑ ℓ ]⊙ Co.[ i ]_∼_) ⊆ Co.[ i ]_∼_
    lemma {i} =
      F ([ ↑ ℓ ]⊙ Co.[ i ]_∼_)               ⊆⟨⟩
      F ([ ↑ ℓ ]⊙ ⟦ S̲t̲e̲p̲ ⟧₂ Co.[ i ]_∼′_)    ⊆⟨ mono (

          [ ↑ ℓ ]⊙ ⟦ S̲t̲e̲p̲ ⟧₂ Co.[ i ]_∼′_         ⊆⟨ (λ _ _ → lower) ⟩
          ⟦ S̲t̲e̲p̲ ⟧₂ Co.[ i ]_∼′_                  ⊆⟨ S̲t̲e̲p̲-monotone (λ _ _ → lift) ⟩∎
          ⟦ S̲t̲e̲p̲ ⟧₂ ([ ↑ ℓ ]⊙ Co.[ i ]_∼′_)       ∎) ⟩

      F (⟦ S̲t̲e̲p̲ ⟧₂ ([ ↑ ℓ ]⊙ Co.[ i ]_∼′_))  ⊆⟨ comp _ ⟩
      ⟦ S̲t̲e̲p̲ ⟧₂ (F ([ ↑ ℓ ]⊙ Co.[ i ]_∼′_))  ⊆⟨ S̲t̲e̲p̲-monotone lemma′ ⟩
      ⟦ S̲t̲e̲p̲ ⟧₂ Co.[ i ]_∼′_                 ⊆⟨ (λ _ _ → id) ⟩∎
      Co.[ i ]_∼_                            ∎

    lemma′ : ∀ {i} → F ([ ↑ ℓ ]⊙ Co.[ i ]_∼′_) ⊆ Co.[ i ]_∼′_
    force (lemma′ {i} p q F∼′pq) {j = j} =
      lemma p q (mono ([ ↑ ℓ ]⊙ Co.[ i ]_∼′_  ⊆⟨ (λ _ _ → lower) ⟩
                       Co.[ i ]_∼′_           ⊆⟨ (λ p q p∼′q → force p∼′q) ⟩
                       Co.[ j ]_∼_            ⊆⟨ (λ _ _ → lift) ⟩∎
                       [ ↑ ℓ ]⊙ Co.[ j ]_∼_   ∎)
                      _ _ F∼′pq)

-- The following four lemmas correspond to Pous and Sangiorgi's
-- Proposition 6.3.11.

-- The identity function is bisimilarity-size-preserving.

id-bisimilarity-size-preserving :
  ∀ {ℓ} → Bisimilarity-size-preserving {ℓ = ℓ} id
id-bisimilarity-size-preserving = id

-- If R is contained in bisimilarity, then const R is
-- bisimilarity-size-preserving.

const-bisimilarity-size-preserving :
  ∀ {ℓ} {R : Rel ℓ Proc} →
  R ⊆ Co._∼_ →
  Bisimilarity-size-preserving (const R)
const-bisimilarity-size-preserving R⊆∼ _ = R⊆∼

-- If F and G are both bisimilarity-size-preserving, then F ∘ G is
-- also bisimilarity-size-preserving.

∘-closure :  ∀ {ℓ} {F G : Trans ℓ Proc} →
  Bisimilarity-size-preserving F →
  Bisimilarity-size-preserving G →
  Bisimilarity-size-preserving (F ∘ G)
∘-closure {F = F} {G} F-pres G-pres {R = R} {i = i} =
 R ⊆ Co.[ i ]_∼_        ↝⟨ G-pres ⟩
 G R ⊆ Co.[ i ]_∼_      ↝⟨ F-pres ⟩□
 F (G R) ⊆ Co.[ i ]_∼_  □

-- If F and G are both bisimilarity-size-preserving, then
-- λ R → F R ∪ G R is also bisimilarity-size-preserving.

∪-closure :
  ∀ {ℓ} {F G : Trans ℓ Proc} →
  Bisimilarity-size-preserving F →
  Bisimilarity-size-preserving G →
  Bisimilarity-size-preserving (λ R → F R ∪ G R)
∪-closure {F = F} {G} F-pres G-pres {R = R} {i = i} =
  R ⊆ Co.[ i ]_∼_          ↝⟨ (λ R⊆∼ _ _ → [ F-pres R⊆∼ _ _ , G-pres R⊆∼ _ _ ]) ⟩□
  F R ∪ G R ⊆ Co.[ i ]_∼_  □

------------------------------------------------------------------------
-- Some examples

-- Up to bisimilarity.

Up-to-bisimilarity : ∀ {ℓ} → Trans ℓ Proc
Up-to-bisimilarity R = Co._∼_ ⊙ R ⊙ Co._∼_

-- Up to bisimilarity is an up-to technique.
--
-- One can perhaps argue that the second part of this proof is less
-- complicated than Pous and Sangiorgi's proof of their Lemma 6.3.13.
-- (Pous and Sangiorgi seem to take for granted that the function is
-- monotone.)

Up-to-bisimilarity-works :
  ∀ {ℓ} → Up-to-technique (Up-to-bisimilarity {ℓ = ℓ})
Up-to-bisimilarity-works = size-preserving→up-to-∀
  Up-to-bisimilarity
  (λ R⊆S _ _ → Σ-map id (Σ-map id (Σ-map id (Σ-map (R⊆S _ _) id))))
  (λ where
     p q (r , p∼r , s , r∼s , s∼q) →
       p  ∼⟨ p∼r ⟩
       r  ∼⟨ r∼s ⟩
       s  ∼⟨ s∼q ⟩■
       q)

-- Up to union.

Up-to-∪ : ∀ {ℓ} → Trans ℓ Proc
Up-to-∪ R = R ∪ Co._∼_

-- Up to union is an up-to technique.

Up-to-∪-works : ∀ {ℓ} → Up-to-technique (Up-to-∪ {ℓ = ℓ})
Up-to-∪-works = size-preserving→up-to-∀
  Up-to-∪
  (λ R⊆S _ _ → ⊎-map (R⊆S _ _) id)
  (λ where
     p q (inj₁ p∼q) → p  ∼⟨ p∼q ⟩■
                      q
     p q (inj₂ p∼q) → p  ∼⟨ p∼q ⟩■
                      q)

-- Up to transitive closure.

Up-to-* : Trans (# 0) Proc
Up-to-* R = R *

-- Up to transitive closure is an up-to technique.

Up-to-*-works : Up-to-technique Up-to-*
Up-to-*-works = size-preserving→up-to₀
  Up-to-*
  (λ R⊆S _ _ → Σ-map id (λ {n} → ^^-mono R⊆S n _ _))
  drop-*
  where
  ^^-mono : ∀ {R S} → R ⊆ S →
            ∀ n → R ^^ n ⊆ S ^^ n
  ^^-mono R⊆S zero    _ _ = id
  ^^-mono R⊆S (suc n) _ _ =
    Σ-map id (Σ-map (R⊆S _ _) (^^-mono R⊆S n _ _))

  drop-* : ∀ {i} p q → (Co.[ i ]_∼_ *) p q → Co.[ i ] p ∼ q
  drop-* p .p (zero  , refl)           = p ■
  drop-* p r  (suc n , q , p∼q , ∼ⁿqr) =
    p  ∼⟨ p∼q ⟩
    q  ∼⟨ drop-* _ _ (n , ∼ⁿqr) ⟩■
    r
