------------------------------------------------------------------------
-- Some results about various forms of coinductively defined weak
-- bisimilarity for the delay monad
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Bisimilarity.Weak.Delay-monad {A : Set} where

open import Delay-monad
open import Delay-monad.Weak-bisimilarity as DW
  using (Weakly-bisimilar; ∞Weakly-bisimilar; force)
open import Equality.Propositional
open import Logical-equivalence using (_⇔_)
open import Prelude

open import Function-universe equality-with-J hiding (id; _∘_)

open import Labelled-transition-system
open Labelled-transition-system.Delay-monad A
open LTS delay-monad hiding (_[_]⟶_)

open import Bisimilarity.Weak.Coinductive delay-monad as BW
  using (force)
import
  Bisimilarity.Weak.Coinductive.Equational-reasoning-instances
open import Bisimilarity.Weak.Coinductive.Equivalent
open import Bisimilarity.Weak.Coinductive.Other delay-monad
import
  Bisimilarity.Weak.Coinductive.Other.Equational-reasoning-instances
open import Equational-reasoning

-- Emulations of the constructors DW.later-cong, DW.laterˡ and
-- DW.laterʳ.

later-cong : ∀ {i x y} →
             [ i ] force x ≈′ force y → [ i ] later x ≈ later y
later-cong x≈′y =
  ⟨ (λ { later⟶ → _ , ⟶→⇒̂ later⟶ , x≈′y })
  , (λ { later⟶ → _ , ⟶→⇒̂ later⟶ , x≈′y })
  ⟩

laterˡ : ∀ {i x y} → [ i ] force x ≈ y → [ i ] later x ≈ y
laterˡ x≈y =
  ⟨ (λ { later⟶ → _ , silent _ done , convert x≈y })
  , Σ-map id (Σ-map later⇒̂ id) ∘ right-to-left x≈y
  ⟩

laterʳ : ∀ {i x y} → [ i ] x ≈ force y → [ i ] x ≈ later y
laterʳ x≈y =
  ⟨ Σ-map id (Σ-map later⇒̂ id) ∘ left-to-right x≈y
  , (λ { later⟶ → _ , silent _ done , convert x≈y })
  ⟩

mutual

  -- The direct definition of weak bisimilarity is contained in the
  -- "other" form of weak bisimilarity obtained from the transition
  -- relation.

  direct→indirect : ∀ {i x y} →
                    Weakly-bisimilar i x y → [ i ] x ≈ y
  direct→indirect DW.now-cong       = reflexive
  direct→indirect (DW.later-cong p) = later-cong (direct→indirect′ p)
  direct→indirect (DW.laterˡ p)     = laterˡ (direct→indirect p)
  direct→indirect (DW.laterʳ p)     = laterʳ (direct→indirect p)

  direct→indirect′ : ∀ {i x y} →
                     ∞Weakly-bisimilar i x y → [ i ] x ≈′ y
  force (direct→indirect′ p) = direct→indirect (force p)

-- If x makes a sequence of zero or more silent transitions to y,
-- then x is weakly bisimilar to y.

⇒→≈ : ∀ {i x y} → x ⇒ y → Weakly-bisimilar i x y
⇒→≈ done               = DW.reflexive _
⇒→≈ (step _ now⟶ tr)   = ⇒→≈ tr
⇒→≈ (step _ later⟶ tr) = DW.laterˡ (⇒→≈ tr)

-- If x makes a non-silent weak transition with the label y, then x
-- is weakly bisimilar to now y.

[just]⇒→≈now : ∀ {i x x′ y} →
               x [ just y ]⇒ x′ → Weakly-bisimilar i x (now y)
[just]⇒→≈now (steps tr now⟶ _) = ⇒→≈ tr

[just]⇒̂→≈now : ∀ {i x x′ y} →
               x [ just y ]⇒̂ x′ → Weakly-bisimilar i x (now y)
[just]⇒̂→≈now (silent () _)
[just]⇒̂→≈now (non-silent _ tr) = [just]⇒→≈now tr

mutual

  -- The "other" definition of weak bisimilarity obtained from the
  -- transition relation is contained in the direct one.

  indirect→direct : ∀ {i} x y → [ i ] x ≈ y → Weakly-bisimilar i x y
  indirect→direct {i} (now x) y =
    [ i ] now x ≈ y                                   ↝⟨ (λ p → left-to-right p now⟶) ⟩
    (∃ λ y′ → y [ later x ]⇒̂ y′ × [ i ] now x ≈′ y′)  ↝⟨ [just]⇒̂→≈now ∘ proj₁ ∘ proj₂ ⟩
    Weakly-bisimilar i y (now x)                      ↝⟨ DW.symmetric ⟩□
    Weakly-bisimilar i (now x) y                      □

  indirect→direct {i} x (now y) =
    [ i ] x ≈ now y                                   ↝⟨ (λ p → right-to-left p now⟶) ⟩
    (∃ λ x′ → x [ later y ]⇒̂ x′ × [ i ] x′ ≈′ now y)  ↝⟨ [just]⇒̂→≈now ∘ proj₁ ∘ proj₂ ⟩□
    Weakly-bisimilar i x (now y)                      □

  indirect→direct (later x) (later y) lx≈ly with left-to-right lx≈ly later⟶
  ... | y′ , non-silent contradiction _    , _     = ⊥-elim (contradiction _)
  ... | y′ , silent _ (step _ later⟶ y⇒y′) , x≈′y′ = DW.later-cong $
                                                     ∞indirect→direct′ y⇒y′ x≈′y′
  ... | y′ , silent _ done                 , x≈′ly with right-to-left lx≈ly later⟶
  ...   | x′ , non-silent contradiction _    , _     = ⊥-elim (contradiction _)
  ...   | x′ , silent _ (step _ later⟶ x⇒x′) , x′≈′y = DW.later-cong $
                                                       DW.∞symmetric $
                                                       ∞indirect→direct′ x⇒x′ $
                                                       symmetric x′≈′y
  ...   | x′ , silent _ done                 , lx≈′y = DW.later-cong $
                                                       DW.∞laterˡʳ⁻¹
                                                         (∞indirect→direct lx≈′y)
                                                         (∞indirect→direct x≈′ly)

  -- Lemmas used by indirect→direct.

  indirect→direct′ : ∀ {i x y y′} →
                     y ⇒ y′ → [ i ] x ≈ y′ → Weakly-bisimilar i x y
  indirect→direct′ done               p = indirect→direct _ _ p
  indirect→direct′ (step _ later⟶ tr) p = DW.laterʳ (indirect→direct′ tr p)
  indirect→direct′ (step () now⟶ _)

  ∞indirect→direct′ : ∀ {i x y y′} →
                      y ⇒ y′ → [ i ] x ≈′ y′ → ∞Weakly-bisimilar i x y
  force (∞indirect→direct′ tr p) = indirect→direct′ tr (force p)

  ∞indirect→direct : ∀ {i x y} →
                     [ i ] x ≈′ y → ∞Weakly-bisimilar i x y
  force (∞indirect→direct p) = indirect→direct _ _ (force p)

-- The direct definition of weak bisimilarity is logically
-- equivalent to the "other" one obtained from the transition
-- relation.

direct⇔indirect : ∀ {i x y} → Weakly-bisimilar i x y ⇔ [ i ] x ≈ y
direct⇔indirect = record
  { to   = direct→indirect
  ; from = indirect→direct _ _
  }

-- The direct definition of weak bisimilarity is logically equivalent
-- to the "first" one obtained from the transition relation. Note that
-- this proof is not size-preserving.

direct⇔indirect′ : ∀ {x y} → x DW.≈ y ⇔ x BW.≈ y
direct⇔indirect′ {x} {y} =
  x DW.≈ y  ↝⟨ direct⇔indirect ⟩
  x ≈ y     ↝⟨ inverse cw⇔cwo ⟩□
  x BW.≈ y  □

-- There is a transitivity proof (for the "other" indirect
-- definition of weak bisimilarity) that preserves the size of the
-- second argument iff A is uninhabited.

size-preserving-transitivityʳ⇔uninhabited :
  (∀ {i} {x y z : Delay A ∞} → x ≈ y → [ i ] y ≈ z → [ i ] x ≈ z) ⇔
  ¬ A
size-preserving-transitivityʳ⇔uninhabited =
  (∀ {i} {x y z : Delay A ∞} → x ≈ y → [ i ] y ≈ z → [ i ] x ≈ z)  ↝⟨ inverse $ implicit-∀-cong-⇔ $ implicit-∀-cong-⇔ $
                                                                      implicit-∀-cong-⇔ $ implicit-∀-cong-⇔ $
                                                                      →-cong-⇔ direct⇔indirect $ →-cong-⇔ direct⇔indirect direct⇔indirect ⟩
  (∀ {i} {x y z : Delay A ∞} →
   x DW.≈ y → Weakly-bisimilar i y z → Weakly-bisimilar i x z)     ↝⟨ DW.size-preserving-transitivityʳ⇔uninhabited ⟩□

  ¬ A                                                              □

-- There is a transitivity proof (for the "other" indirect
-- definition of weak bisimilarity) that preserves the size of the
-- first argument iff A is uninhabited.

size-preserving-transitivityˡ⇔uninhabited :
  (∀ {i} {x y z : Delay A ∞} → [ i ] x ≈ y → y ≈ z → [ i ] x ≈ z) ⇔
  ¬ A
size-preserving-transitivityˡ⇔uninhabited =
  (∀ {i} {x y z : Delay A ∞} → [ i ] x ≈ y → y ≈ z → [ i ] x ≈ z)  ↝⟨ inverse $ implicit-∀-cong-⇔ $ implicit-∀-cong-⇔ $
                                                                      implicit-∀-cong-⇔ $ implicit-∀-cong-⇔ $
                                                                      →-cong-⇔ direct⇔indirect $ →-cong-⇔ direct⇔indirect direct⇔indirect ⟩
  (∀ {i} {x y z : Delay A ∞} →
   Weakly-bisimilar i x y → y DW.≈ z → Weakly-bisimilar i x z)     ↝⟨ DW.size-preserving-transitivityˡ⇔uninhabited ⟩□

  ¬ A                                                              □

private

  -- If A is uninhabited, then BW._≈_ is trivial.

  uninhabited→trivial : ¬ A → ∀ x y → x BW.≈ y
  uninhabited→trivial =
    ¬ A                 ↝⟨ DW.uninhabited→trivial ⟩
    (∀ x y → x DW.≈ y)  ↝⟨ ∀-cong-→ (λ _ → ∀-cong-→ λ _ → _⇔_.to direct⇔indirect′) ⟩
    (∀ x y → x BW.≈ y)  □

-- The function cwo⇒cw translating from the "other" indirect
-- definition of weak bisimilarity to the first indirect one can be
-- made size-preserving iff A is uninhabited.

size-preserving-cwo⇒cw⇔uninhabited :
  (∀ {i p q} → [ i ] p ≈ q → BW.[ i ] p ≈ q) ⇔ ¬ A
size-preserving-cwo⇒cw⇔uninhabited = record
  { to =
      (∀ {i p q} → [ i ] p ≈ q → BW.[ i ] p ≈ q)                       ↝⟨ (λ cwo⇒cw x≈y y≈z → cw⇒cwo (transitive (cwo⇒cw x≈y) (cwo⇒cw y≈z))) ⟩
      (∀ {i} {x y z : Delay A ∞} → x ≈ y → [ i ] y ≈ z → [ i ] x ≈ z)  ↝⟨ _⇔_.to size-preserving-transitivityʳ⇔uninhabited ⟩□
      ¬ A                                                              □
  ; from =
      ¬ A                                         ↝⟨ uninhabited→trivial ⟩
      (∀ x y → x BW.≈ y)                          ↝⟨ (λ trivial {_ _ _} _ → trivial _ _) ⟩□
      (∀ {i p q} → [ i ] p ≈ q → BW.[ i ] p ≈ q)  □
  }

-- One can define a size-preserving "later-cong" function for the
-- "first" indirect definition of weak bisimilarity iff A is
-- uninhabited.

size-preserving-later-cong⇔uninhabited :
  (∀ {i x y} → BW.[ i ] force x ≈′ force y → BW.[ i ] later x ≈ later y)
    ⇔
  ¬ A
size-preserving-later-cong⇔uninhabited = record
  { to   = Later-cong                ↝⟨ (λ later-cong → now≈never (λ {i} → later-cong {i})) ⟩
           (∀ x → now x BW.≈ never)  ↝⟨ ∀-cong-→ (λ _ → _⇔_.from direct⇔indirect′) ⟩
           (∀ x → now x DW.≈ never)  ↝⟨ (λ hyp → DW.now≉never ∘ hyp) ⟩□
           ¬ A                       □
  ; from = ¬ A                 ↝⟨ uninhabited→trivial ⟩
           (∀ x y → x BW.≈ y)  ↝⟨ (λ trivial {_ _ _} _ → trivial _ _) ⟩□
           Later-cong          □
  }
  where
  Later-cong =
    ∀ {i x y} → BW.[ i ] force x ≈′ force y → BW.[ i ] later x ≈ later y

  module _ (later-cong : Later-cong) where

    mutual

      now≈never : ∀ {i} x → BW.[ i ] now x ≈ never
      now≈never x =
        now x                             ∼⟨ cwo⇒cw (laterʳ reflexive) ⟩
        later (record { force = now x })  ∼⟨ later-cong (now≈never′ x) ⟩■
        never

      now≈never′ : ∀ {i} x → BW.[ i ] now x ≈′ never
      force (now≈never′ x) = now≈never x
