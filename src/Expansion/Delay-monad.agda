------------------------------------------------------------------------
-- Some results related to expansion for the delay monad
------------------------------------------------------------------------

{-# OPTIONS --sized-types #-}

open import Prelude

module Expansion.Delay-monad {a} {A : Type a} where

open import Delay-monad
open import Delay-monad.Bisimilarity as D using (force)
import Delay-monad.Bisimilarity.Negative as DN
open import Equality.Propositional
open import Logical-equivalence using (_⇔_)
open import Prelude.Size

open import Function-universe equality-with-J hiding (id; _∘_)
open import Function-universe.Size equality-with-J

import Bisimilarity.Delay-monad as SD
open import Equational-reasoning
import Expansion.Equational-reasoning-instances
open import Labelled-transition-system.Delay-monad A

open import Bisimilarity delay-monad using ([_]_∼_)
open import Expansion delay-monad

------------------------------------------------------------------------
-- The direct and the indirect definitions of expansion are pointwise
-- logically equivalent

-- Emulations of the constructors D.later and D.laterˡ.

later-cong : ∀ {i x y} →
             [ i ] force x ≳′ force y → [ i ] later x ≳ later y
later-cong x≳′y =
  ⟨ (λ { later → _ , ⟶→⟶̂   later , x≳′y })
  , (λ { later → _ , ⟶→[]⇒ later , x≳′y })
  ⟩

laterˡ : ∀ {i x y} → [ i ] force x ≳ y → [ i ] later x ≳ y
laterˡ x≳y =
  ⟨ (λ { later → _ , done _ , convert {a = a} x≳y })
  , Σ-map id (Σ-map later[]⇒ id) ∘ right-to-left x≳y
  ⟩

-- The direct definition of expansion is contained in the one
-- obtained from the transition relation.

direct→indirect : ∀ {i x y} →
                  D.[ i ] x ≳ y → [ i ] x ≳ y
direct→indirect D.now        = reflexive
direct→indirect (D.later  p) = later-cong λ { .force →
                                 direct→indirect (force p) }
direct→indirect (D.laterˡ p) = laterˡ (direct→indirect p)

-- If x makes a sequence of zero or more silent transitions to y, then
-- x is an expansion of y.

⇒→≳ : ∀ {i x y} → x ⇒ y → D.[ i ] x ≳ y
⇒→≳ done               = D.reflexive _
⇒→≳ (step _  later tr) = D.laterˡ (⇒→≳ tr)
⇒→≳ (step () now   tr)

-- If x makes a non-silent transition with the label y, then x is an
-- expansion of now y.

[just]⟶→≳now : ∀ {i x x′ y} → x [ just y ]⟶ x′ → D.[ i ] x ≳ now y
[just]⟶→≳now now = D.reflexive _

[just]⇒→≳now : ∀ {i x x′ y} → x [ just y ]⇒ x′ → D.[ i ] x ≳ now y
[just]⇒→≳now (steps tr now _) = ⇒→≳ tr

[just]⇒̂→≳now : ∀ {i x x′ y} → x [ just y ]⇒̂ x′ → D.[ i ] x ≳ now y
[just]⇒̂→≳now (silent () _)
[just]⇒̂→≳now (non-silent _ tr) = [just]⇒→≳now tr

[just]⟶̂→≳now : ∀ {i x x′ y} → x [ just y ]⟶̂ x′ → D.[ i ] x ≳ now y
[just]⟶̂→≳now (done ())
[just]⟶̂→≳now (step tr) = [just]⇒̂→≳now (⟶→⇒̂ tr)

-- The definition of expansion obtained from the transition relation
-- is contained in the direct one.

indirect→direct : ∀ {i} x y → [ i ] x ≳ y → D.[ i ] x ≳ y
indirect→direct {i} (now x) y =
  ([ i ] now x ≳ y)                                ↝⟨ (λ p → left-to-right p now) ⟩
  (∃ λ y′ → y [ just x ]⟶̂ y′ × [ i ] now x ≳′ y′)  ↝⟨ sym ∘ [just]⟶̂→≡now ∘ proj₁ ∘ proj₂ ⟩
  now x ≡ y                                        ↝⟨ (λ { refl → D.reflexive _ }) ⟩□
  D.[ i ] now x ≳ y                                □

indirect→direct {i} x (now y) =
  [ i ] x ≳ now y                                  ↝⟨ (λ p → right-to-left p now) ⟩
  (∃ λ x′ → x [ just y ]⇒ x′ × [ i ] x′ ≳′ now y)  ↝⟨ [just]⇒→≳now ∘ proj₁ ∘ proj₂ ⟩□
  D.[ i ] x ≳ now y                                □

indirect→direct (later x) (later y) lx≳ly =
  case left-to-right lx≳ly later of λ where
    (_ , step later , x≳′y) → D.later λ { .force {j} →
                                indirect→direct _ _
                                  (force x≳′y {j = j}) }
    (_ , done _     , x≳′ly) →
      let x′ , lx⇒x′ , x′≳′y = right-to-left lx≳ly later
      in lemma x≳′ly ([]⇒→⇒ _ lx⇒x′) x′≳′y
  where
  indirect→direct′ : ∀ {i x x′ y} →
                     x ⇒ x′ → [ i ] x′ ≳ y → D.[ i ] x ≳ y
  indirect→direct′ done               p = indirect→direct _ _ p
  indirect→direct′ (step _  later tr) p = D.laterˡ
                                            (indirect→direct′ tr p)
  indirect→direct′ (step () now   _)

  lemma :
    ∀ {i x x′} →
    [ i ] force x ≳′ later y →
    later x ⇒ x′ → [ i ] x′ ≳′ force y →
    D.[ i ] later x ≳ later y
  lemma x≳′ly done lx≳′y =
    D.later λ { .force →
      D.laterˡʳ⁻¹
        (indirect→direct _ _ (force lx≳′y))
        (indirect→direct _ _ (force x≳′ly)) }
  lemma x≳′ly (step _ later x⇒x′) x′≳′y =
    D.later λ { .force →
      indirect→direct′ x⇒x′ (force x′≳′y) }

-- The direct definition of the expansion relation is logically
-- equivalent to the one obtained from the transition relation.
--
-- TODO: Are the two definitions isomorphic?

direct⇔indirect : ∀ {i x y} → D.[ i ] x ≳ y ⇔ [ i ] x ≳ y
direct⇔indirect = record
  { to   = direct→indirect
  ; from = indirect→direct _ _
  }

------------------------------------------------------------------------
-- Some non-existence results

Now≳later-now = ∀ x → now x ≳ later (record { force = now x })

now≳later-now⇔uninhabited : Now≳later-now ⇔ ¬ A
now≳later-now⇔uninhabited =
  Now≳later-now     ↝⟨ inverse $ ∀-cong _ (λ _ → direct⇔indirect) ⟩
  DN.Now≳later-now  ↝⟨ DN.now≳later-now⇔uninhabited ⟩□
  ¬ A               □

Laterˡ⁻¹ = ∀ {x y} → later x ≳ y → force x ≳ y

laterˡ⁻¹⇔uninhabited : Laterˡ⁻¹ ⇔ ¬ A
laterˡ⁻¹⇔uninhabited =
  Laterˡ⁻¹       ↝⟨ inverse $ implicit-∀-cong _ $ implicit-∀-cong _ $ →-cong _ direct⇔indirect direct⇔indirect ⟩
  DN.Laterˡ⁻¹-≳  ↝⟨ DN.laterˡ⁻¹-≳⇔uninhabited ⟩□
  ¬ A            □

Laterʳ⁻¹-∼≳ =
  ∀ {i x} →
  [ i ] never ∼ later (record { force = now x }) →
  [ i ] never ≳ now x

size-preserving-laterʳ⁻¹-∼≳⇔uninhabited : Laterʳ⁻¹-∼≳ ⇔ ¬ A
size-preserving-laterʳ⁻¹-∼≳⇔uninhabited =
  Laterʳ⁻¹-∼≳     ↝⟨ inverse $ implicit-∀-size-cong _ $ implicit-∀-cong _ $ →-cong _ SD.direct⇔indirect direct⇔indirect ⟩
  DN.Laterʳ⁻¹-∼≳  ↝⟨ DN.size-preserving-laterʳ⁻¹-∼≳⇔uninhabited ⟩□
  ¬ A             □

Laterʳ⁻¹ = ∀ {i x y} → [ i ] x ≳ later y → [ i ] x ≳ force y

size-preserving-laterʳ⁻¹⇔uninhabited : Laterʳ⁻¹ ⇔ ¬ A
size-preserving-laterʳ⁻¹⇔uninhabited =
  Laterʳ⁻¹       ↝⟨ inverse $ implicit-∀-size-cong _ $ implicit-∀-cong _ $ implicit-∀-cong _ $ →-cong _ direct⇔indirect direct⇔indirect ⟩
  DN.Laterʳ⁻¹-≳  ↝⟨ DN.size-preserving-laterʳ⁻¹-≳⇔uninhabited ⟩□
  ¬ A            □

Transitivity-∼≳ˡ =
  ∀ {i} {x y z : Delay A ∞} →
  [ i ] x ∼ y → y ≳ z → [ i ] x ≳ z

size-preserving-transitivity-∼≳ˡ⇔uninhabited : Transitivity-∼≳ˡ ⇔ ¬ A
size-preserving-transitivity-∼≳ˡ⇔uninhabited =
  Transitivity-∼≳ˡ     ↝⟨ inverse $ implicit-∀-size-cong _ $ implicit-∀-cong _ $ implicit-∀-cong _ $ implicit-∀-cong _ $
                          →-cong _ SD.direct⇔indirect (→-cong _ direct⇔indirect direct⇔indirect) ⟩
  DN.Transitivity-∼≳ˡ  ↝⟨ DN.size-preserving-transitivity-∼≳ˡ⇔uninhabited ⟩□
  ¬ A                  □

Transitivityˡ =
  ∀ {i} {x y z : Delay A ∞} →
  [ i ] x ≳ y → y ≳ z → [ i ] x ≳ z

size-preserving-transitivityˡ⇔uninhabited : Transitivityˡ ⇔ ¬ A
size-preserving-transitivityˡ⇔uninhabited =
  Transitivityˡ       ↝⟨ inverse $ implicit-∀-size-cong _ $ implicit-∀-cong _ $ implicit-∀-cong _ $ implicit-∀-cong _ $
                         →-cong _ direct⇔indirect (→-cong _ direct⇔indirect direct⇔indirect) ⟩
  DN.Transitivity-≳ˡ  ↝⟨ DN.size-preserving-transitivity-≳ˡ⇔uninhabited ⟩□
  ¬ A                 □

Transitivity =
  ∀ {i} {x y z : Delay A ∞} →
  [ i ] x ≳ y → [ i ] y ≳ z → [ i ] x ≳ z

size-preserving-transitivity⇔uninhabited : Transitivity ⇔ ¬ A
size-preserving-transitivity⇔uninhabited =
  Transitivity       ↝⟨ inverse $ implicit-∀-size-cong _ $ implicit-∀-cong _ $ implicit-∀-cong _ $ implicit-∀-cong _ $
                        →-cong _ direct⇔indirect $ →-cong _ direct⇔indirect direct⇔indirect ⟩
  DN.Transitivity-≳  ↝⟨ DN.size-preserving-transitivity-≳⇔uninhabited ⟩□
  ¬ A                □
