------------------------------------------------------------------------
-- Some results about various forms of coinductively defined weak
-- bisimilarity for the delay monad
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Bisimilarity.Weak.Delay-monad {a} {A : Set a} where

open import Delay-monad
import Delay-monad.Expansion as DE
open import Delay-monad.Weak-bisimilarity as DW using (force)
open import Equality.Propositional
open import Logical-equivalence using (_⇔_)
open import Prelude

open import Function-universe equality-with-J hiding (id; _∘_)

import Bisimilarity.Coinductive.Delay-monad as SD
import
  Bisimilarity.Weak.Coinductive.Equational-reasoning-instances
open import Bisimilarity.Weak.Coinductive.Equivalent
import
  Bisimilarity.Weak.Coinductive.Other.Equational-reasoning-instances
open import Equational-reasoning
import Expansion.Delay-monad as ED
open import Labelled-transition-system.Delay-monad A

open import Bisimilarity.Coinductive delay-monad using ([_]_∼_)
open import Bisimilarity.Weak.Coinductive delay-monad as BW
  using (force)
open import Bisimilarity.Weak.Coinductive.Other delay-monad
open import Expansion delay-monad as BE using ([_]_≳_; _≳_)

------------------------------------------------------------------------
-- Several definitions of weak bisimilarity are pointwise logically
-- equivalent

-- Emulations of the constructors DW.later, DW.laterˡ and DW.laterʳ.

later-cong : ∀ {i x y} →
             [ i ] force x ≈′ force y → [ i ] later x ≈ later y
later-cong x≈′y =
  ⟨ (λ { later⟶ → _ , ⟶→⇒̂ later⟶ , x≈′y })
  , (λ { later⟶ → _ , ⟶→⇒̂ later⟶ , x≈′y })
  ⟩

laterˡ : ∀ {i x y} → [ i ] force x ≈ y → [ i ] later x ≈ y
laterˡ x≈y =
  ⟨ (λ { later⟶ → _ , silent _ done , convert {a = a} x≈y })
  , Σ-map id (Σ-map later⇒̂ id) ∘ right-to-left x≈y
  ⟩

laterʳ : ∀ {i x y} → [ i ] x ≈ force y → [ i ] x ≈ later y
laterʳ x≈y =
  ⟨ Σ-map id (Σ-map later⇒̂ id) ∘ left-to-right x≈y
  , (λ { later⟶ → _ , silent _ done , convert {a = a} x≈y })
  ⟩

-- The direct definition of weak bisimilarity is contained in the
-- "other" form of weak bisimilarity obtained from the transition
-- relation.

direct→indirect : ∀ {i x y} →
                  DW.[ i ] x ≈ y → [ i ] x ≈ y
direct→indirect DW.now        = reflexive
direct→indirect (DW.later  p) = later-cong λ { .force →
                                  direct→indirect (force p) }
direct→indirect (DW.laterˡ p) = laterˡ (direct→indirect p)
direct→indirect (DW.laterʳ p) = laterʳ (direct→indirect p)

mutual

  -- The "other" definition of weak bisimilarity obtained from the
  -- transition relation is contained in the direct one.

  indirect→direct : ∀ {i} x y → [ i ] x ≈ y → DW.[ i ] x ≈ y
  indirect→direct {i} (now x) y =
    [ i ] now x ≈ y                                  ↝⟨ (λ p → left-to-right p now⟶) ⟩
    (∃ λ y′ → y [ just x ]⇒̂ y′ × [ i ] now x ≈′ y′)  ↝⟨ DE.≳→≈ ∘ ED.[just]⇒̂→≳now ∘ proj₁ ∘ proj₂ ⟩
    DW.[ i ] y ≈ now x                               ↝⟨ DW.symmetric ⟩□
    DW.[ i ] now x ≈ y                               □

  indirect→direct {i} x (now y) =
    [ i ] x ≈ now y                                  ↝⟨ (λ p → right-to-left p now⟶) ⟩
    (∃ λ x′ → x [ just y ]⇒̂ x′ × [ i ] x′ ≈′ now y)  ↝⟨ DE.≳→≈ ∘ ED.[just]⇒̂→≳now ∘ proj₁ ∘ proj₂ ⟩□
    DW.[ i ] x ≈ now y                               □

  indirect→direct (later x) (later y) lx≈ly
    with left-to-right lx≈ly later⟶

  ... | y′ , non-silent contradiction _ , _ =
    ⊥-elim (contradiction _)

  ... | y′ , silent _ (step _ later⟶ y⇒y′) , x≈′y′ =
    DW.later λ { .force →
      indirect→direct′ y⇒y′ (force x≈′y′) }

  ... | y′ , silent _ done , x≈′ly
    with right-to-left lx≈ly later⟶

  ...   | x′ , non-silent contradiction _ , _ =
    ⊥-elim (contradiction _)

  ...   | x′ , silent _ (step _ later⟶ x⇒x′) , x′≈′y =
    DW.later λ { .force →
      DW.symmetric $
      indirect→direct′ x⇒x′ $
      symmetric (force x′≈′y) }

  ...   | x′ , silent _ done , lx≈′y =
    DW.later λ { .force →
      DW.laterˡʳ⁻¹
        (indirect→direct _ _ (force lx≈′y))
        (indirect→direct _ _ (force x≈′ly)) }

  private

    -- A lemma used by indirect→direct.

    indirect→direct′ : ∀ {i x y y′} →
                       y ⇒ y′ → [ i ] x ≈ y′ → DW.[ i ] x ≈ y
    indirect→direct′ done               p = indirect→direct _ _ p
    indirect→direct′ (step _ later⟶ tr) p = DW.laterʳ (indirect→direct′ tr p)
    indirect→direct′ (step () now⟶ _)

-- The direct definition of weak bisimilarity is logically
-- equivalent to the "other" one obtained from the transition
-- relation.
--
-- TODO: Are the two definitions isomorphic?

direct⇔indirect : ∀ {i x y} → DW.[ i ] x ≈ y ⇔ [ i ] x ≈ y
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

------------------------------------------------------------------------
-- A non-existence result for the "first" indirect definition of weak
-- bisimilarity

private

  -- If A is uninhabited, then BW._≈_ is trivial.

  uninhabited→trivial : ¬ A → ∀ x y → x BW.≈ y
  uninhabited→trivial =
    ¬ A                 ↝⟨ DW.uninhabited→trivial ⟩
    (∀ x y → x DW.≈ y)  ↝⟨ ∀-cong _ (λ _ → ∀-cong _ λ _ → _⇔_.to direct⇔indirect′) ⟩
    (∀ x y → x BW.≈ y)  □

-- One can define a size-preserving "later-cong" function iff A is
-- uninhabited.

Later-cong =
  ∀ {i x y} →
  BW.[ i ] force x ≈′ force y → BW.[ i ] later x ≈ later y

size-preserving-later-cong⇔uninhabited : Later-cong ⇔ ¬ A
size-preserving-later-cong⇔uninhabited = record
  { to   = Later-cong                ↝⟨ (λ later-cong → now≈never (λ {i} → later-cong {i})) ⟩
           (∀ x → now x BW.≈ never)  ↝⟨ ∀-cong _ (λ _ → _⇔_.from direct⇔indirect′) ⟩
           (∀ x → now x DW.≈ never)  ↝⟨ (λ hyp → DW.now≉never ∘ hyp) ⟩□
           ¬ A                       □
  ; from = ¬ A                 ↝⟨ uninhabited→trivial ⟩
           (∀ x y → x BW.≈ y)  ↝⟨ (λ trivial {_ _ _} _ → trivial _ _) ⟩□
           Later-cong          □
  }
  where

  module _ (later-cong : Later-cong) where

    now≈never : ∀ {i} x → BW.[ i ] now x ≈ never
    now≈never x =
      now x                         ∼⟨ cwo⇒cw (laterʳ reflexive) ⟩
      later (λ { .force → now x })  ∼⟨ later-cong (λ { .force → now≈never x }) ⟩■
      never

------------------------------------------------------------------------
-- Some non-existence results for the "other" indirect definition of
-- weak bisimilarity

-- There is a transitivity proof that takes weak bisimilarity and
-- expansion to expansion iff A is uninhabited.

Transitivity-≈≳ = {x y z : Delay A ∞} → x ≈ y → y ≳ z → x ≳ z
Transitivity-≳≈ = {x y z : Delay A ∞} → x ≳ y → y ≈ z → x ≳ z

transitive-≈≳⇔uninhabited : Transitivity-≈≳ ⇔ ¬ A
transitive-≈≳⇔uninhabited =
  Transitivity-≈≳     ↝⟨ inverse $ implicit-∀-cong _ $ implicit-∀-cong _ $ implicit-∀-cong _ $
                         →-cong _ direct⇔indirect (→-cong _ ED.direct⇔indirect ED.direct⇔indirect) ⟩
  DE.Transitivity-≈≳  ↝⟨ DE.transitive-≈≳⇔uninhabited ⟩□
  ¬ A                 □

transitive-≳≈⇔uninhabited : Transitivity-≳≈ ⇔ ¬ A
transitive-≳≈⇔uninhabited =
  Transitivity-≳≈     ↝⟨ inverse $ implicit-∀-cong _ $ implicit-∀-cong _ $ implicit-∀-cong _ $
                         →-cong _ ED.direct⇔indirect (→-cong _ direct⇔indirect ED.direct⇔indirect) ⟩
  DE.Transitivity-≳≈  ↝⟨ DE.transitive-≳≈⇔uninhabited ⟩□
  ¬ A                 □

-- There is a transitivity proof that preserves the size of the second
-- argument iff A is uninhabited.

Transitivityʳ =
  ∀ {i} {x y z : Delay A ∞} →
  x ≈ y → [ i ] y ≈ z → [ i ] x ≈ z

size-preserving-transitivityʳ⇔uninhabited : Transitivityʳ ⇔ ¬ A
size-preserving-transitivityʳ⇔uninhabited =
  Transitivityʳ     ↝⟨ inverse $ implicit-∀-cong _ $ implicit-∀-cong _ $ implicit-∀-cong _ $ implicit-∀-cong _ $
                       →-cong _ direct⇔indirect $ →-cong _ direct⇔indirect direct⇔indirect ⟩
  DW.Transitivityʳ  ↝⟨ DW.size-preserving-transitivityʳ⇔uninhabited ⟩□
  ¬ A               □

-- There is a transitivity proof that preserves the size of the first
-- argument iff A is uninhabited.

Transitivityˡ =
  ∀ {i} {x y z : Delay A ∞} →
  [ i ] x ≈ y → y ≈ z → [ i ] x ≈ z

size-preserving-transitivityˡ⇔uninhabited : Transitivityˡ ⇔ ¬ A
size-preserving-transitivityˡ⇔uninhabited =
  Transitivityˡ     ↝⟨ inverse $ implicit-∀-cong _ $ implicit-∀-cong _ $ implicit-∀-cong _ $ implicit-∀-cong _ $
                       →-cong _ direct⇔indirect $ →-cong _ direct⇔indirect direct⇔indirect ⟩
  DW.Transitivityˡ  ↝⟨ DW.size-preserving-transitivityˡ⇔uninhabited ⟩□
  ¬ A               □

-- There is a transitivity proof that preserves the size of the second
-- argument, a strong bisimilarity, iff A is uninhabited.

Transitivity-≈∼ʳ =
  ∀ {i} {x y z : Delay A ∞} →
  x ≈ y → [ i ] y ∼ z → [ i ] x ≈ z

size-preserving-transitivity-≈∼ʳ⇔uninhabited : Transitivity-≈∼ʳ ⇔ ¬ A
size-preserving-transitivity-≈∼ʳ⇔uninhabited =
  Transitivity-≈∼ʳ     ↝⟨ inverse $ implicit-∀-cong _ $ implicit-∀-cong _ $ implicit-∀-cong _ $ implicit-∀-cong _ $
                          →-cong _ direct⇔indirect $ →-cong _ SD.direct⇔indirect direct⇔indirect ⟩
  DW.Transitivity-≈∼ʳ  ↝⟨ DW.size-preserving-transitivity-≈∼ʳ⇔uninhabited ⟩□
  ¬ A                  □

-- There is a transitivity proof that preserves the size of the first
-- argument, a strong bisimilarity, iff A is uninhabited.

Transitivity-∼≈ˡ =
  ∀ {i} {x y z : Delay A ∞} →
  [ i ] x ∼ y → y ≈ z → [ i ] x ≈ z

size-preserving-transitivity-∼≈ˡ⇔uninhabited : Transitivity-∼≈ˡ ⇔ ¬ A
size-preserving-transitivity-∼≈ˡ⇔uninhabited =
  Transitivity-∼≈ˡ     ↝⟨ inverse $ implicit-∀-cong _ $ implicit-∀-cong _ $ implicit-∀-cong _ $ implicit-∀-cong _ $
                          →-cong _ SD.direct⇔indirect $ →-cong _ direct⇔indirect direct⇔indirect ⟩
  DW.Transitivity-∼≈ˡ  ↝⟨ DW.size-preserving-transitivity-∼≈ˡ⇔uninhabited ⟩□
  ¬ A                  □

-- There is a transitivity-like proof that preserves the size of the
-- first argument, an expansion, iff A is uninhabited.

Transitivity-≳≈ˡ =
  ∀ {i} {x y z : Delay A ∞} →
  [ i ] x ≳ y → y ≈ z → [ i ] x ≈ z

size-preserving-transitivity-≳≈ˡ⇔uninhabited : Transitivity-≳≈ˡ ⇔ ¬ A
size-preserving-transitivity-≳≈ˡ⇔uninhabited =
  Transitivity-≳≈ˡ     ↝⟨ inverse $ implicit-∀-cong _ $ implicit-∀-cong _ $ implicit-∀-cong _ $ implicit-∀-cong _ $
                          →-cong _ ED.direct⇔indirect (→-cong _ direct⇔indirect direct⇔indirect) ⟩
  DE.Transitivity-≳≈ˡ  ↝⟨ DE.size-preserving-transitivity-≳≈ˡ⇔uninhabited ⟩□
  ¬ A                  □

-- There is a transitivity-like proof that preserves the size of the
-- second argument, an expansion, iff A is uninhabited.

Transitivity-≈≲ʳ =
  ∀ {i} {x y z : Delay A ∞} →
  x ≈ y → [ i ] z ≳ y → [ i ] x ≈ z

size-preserving-transitivity-≈≲ʳ⇔uninhabited : Transitivity-≈≲ʳ ⇔ ¬ A
size-preserving-transitivity-≈≲ʳ⇔uninhabited =
  Transitivity-≈≲ʳ     ↝⟨ inverse $ implicit-∀-cong _ $ implicit-∀-cong _ $ implicit-∀-cong _ $ implicit-∀-cong _ $
                          →-cong _ direct⇔indirect (→-cong _ ED.direct⇔indirect direct⇔indirect) ⟩
  DE.Transitivity-≈≲ʳ  ↝⟨ DE.size-preserving-transitivity-≈≲ʳ⇔uninhabited ⟩□
  ¬ A                  □

-- There is a transitivity-like proof that preserves the size of the
-- first argument, and takes an expansion as the second argument, iff
-- A is uninhabited.

Transitivity-≈≳ˡ =
  ∀ {i} {x y z : Delay A ∞} →
  [ i ] x ≈ y → y ≳ z → [ i ] x ≈ z

size-preserving-transitivity-≈≳ˡ⇔uninhabited : Transitivity-≈≳ˡ ⇔ ¬ A
size-preserving-transitivity-≈≳ˡ⇔uninhabited =
  Transitivity-≈≳ˡ     ↝⟨ inverse $ implicit-∀-cong _ $ implicit-∀-cong _ $ implicit-∀-cong _ $ implicit-∀-cong _ $
                          →-cong _ direct⇔indirect (→-cong _ ED.direct⇔indirect direct⇔indirect) ⟩
  DE.Transitivity-≈≳ˡ  ↝⟨ DE.size-preserving-transitivity-≈≳ˡ⇔uninhabited ⟩□
  ¬ A                  □

------------------------------------------------------------------------
-- A non-existence result for both indirect definitions of weak
-- bisimilarity

-- The function cwo⇒cw translating from the "other" indirect
-- definition of weak bisimilarity to the first indirect one can be
-- made size-preserving iff A is uninhabited.

size-preserving-cwo⇒cw⇔uninhabited :
  (∀ {i p q} → [ i ] p ≈ q → BW.[ i ] p ≈ q) ⇔ ¬ A
size-preserving-cwo⇒cw⇔uninhabited = record
  { to =
      (∀ {i p q} → [ i ] p ≈ q → BW.[ i ] p ≈ q)  ↝⟨ (λ cwo⇒cw x≈y y≈z → cw⇒cwo (transitive {a = a} (cwo⇒cw x≈y) (cwo⇒cw y≈z))) ⟩
      Transitivityʳ                               ↝⟨ _⇔_.to size-preserving-transitivityʳ⇔uninhabited ⟩□
      ¬ A                                         □
  ; from =
      ¬ A                                         ↝⟨ uninhabited→trivial ⟩
      (∀ x y → x BW.≈ y)                          ↝⟨ (λ trivial {_ _ _} _ → trivial _ _) ⟩□
      (∀ {i p q} → [ i ] p ≈ q → BW.[ i ] p ≈ q)  □
  }

------------------------------------------------------------------------
-- More lemmas

-- If x and y both make non-silent transitions of the same kind,
-- then they are weakly bisimilar.

⟶-with-equal-labels→≈ :
  ∀ {x x′ y y′ μ} →
  ¬ Silent μ → x [ μ ]⟶ x′ → y [ μ ]⟶ y′ → x ≈ y
⟶-with-equal-labels→≈ _  now⟶   now⟶ = reflexive
⟶-with-equal-labels→≈ ¬s later⟶ _    = ⊥-elim (¬s _)

[]⇒-with-equal-labels→≈ :
  ∀ {x x′ y y′ μ} →
  ¬ Silent μ → x [ μ ]⇒ x′ → y [ μ ]⇒ y′ → x ≈ y
[]⇒-with-equal-labels→≈
  {x = x} {y = y} ¬s
  (steps {p′ = x′} x⇒x′ x′⟶x″ x″⇒x‴)
  (steps {p′ = y′} y⇒y′ y′⟶y″ y″⇒y‴) =

  x   ∼⟨ direct→indirect (DE.≳→≈ (ED.⇒→≳ x⇒x′)) ⟩
  x′  ∼⟨ ⟶-with-equal-labels→≈ ¬s x′⟶x″ y′⟶y″ ⟩
  y′  ∼⟨ symmetric (direct→indirect (DE.≳→≈ (ED.⇒→≳ y⇒y′))) ⟩■
  y

⇒̂-with-equal-labels→≈ :
  ∀ {x x′ y y′ μ} →
  ¬ Silent μ → x [ μ ]⇒̂ x′ → y [ μ ]⇒̂ y′ → x ≈ y
⇒̂-with-equal-labels→≈ ¬s (non-silent _ x⇒x′) (non-silent _ y⇒y′) =
  []⇒-with-equal-labels→≈ ¬s x⇒x′ y⇒y′
⇒̂-with-equal-labels→≈ ¬s   (silent s _) = ⊥-elim (¬s s)
⇒̂-with-equal-labels→≈ ¬s _ (silent s _) = ⊥-elim (¬s s)

⟶̂-with-equal-labels→≈ :
  ∀ {x x′ y y′ μ} →
  ¬ Silent μ → x [ μ ]⟶̂ x′ → y [ μ ]⟶̂ y′ → x ≈ y
⟶̂-with-equal-labels→≈ ¬s x⟶̂x′ y⟶̂y′ =
  ⇒̂-with-equal-labels→≈ ¬s (⟶̂→⇒̂ x⟶̂x′) (⟶̂→⇒̂ y⟶̂y′)
