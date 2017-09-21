------------------------------------------------------------------------
-- Some results related to expansion for the delay monad
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Expansion.Delay-monad {A : Set} where

open import Delay-monad
open import Delay-monad.Expansion as DE using (force)
open import Equality.Propositional
open import Logical-equivalence using (_⇔_)
open import Prelude

open import Function-universe equality-with-J hiding (id; _∘_)

import Bisimilarity.Coinductive.Delay-monad as SD
open import Equational-reasoning
import Expansion.Equational-reasoning-instances
open import Labelled-transition-system.Delay-monad A

open import Bisimilarity.Coinductive delay-monad using ([_]_∼_)
open import Expansion delay-monad

------------------------------------------------------------------------
-- The direct and the indirect definitions of expansion are pointwise
-- logically equivalent

-- Emulations of the constructors DE.later-cong and DE.laterˡ.

later-cong : ∀ {i x y} →
             [ i ] force x ≳′ force y → [ i ] later x ≳ later y
later-cong x≳′y =
  ⟨ (λ { later⟶ → _ , ⟶→⟶̂ later⟶ , x≳′y })
  , (λ { later⟶ → _ , ⟶→⇒̂ later⟶ , x≳′y })
  ⟩

laterˡ : ∀ {i x y} → [ i ] force x ≳ y → [ i ] later x ≳ y
laterˡ x≳y =
  ⟨ (λ { later⟶ → _ , done _ , convert x≳y })
  , Σ-map id (Σ-map later⇒̂ id) ∘ right-to-left x≳y
  ⟩

mutual

  -- The direct definition of expansion is contained in the one
  -- obtained from the transition relation.

  direct→indirect : ∀ {i x y} →
                    DE.Expansion i x y → [ i ] x ≳ y
  direct→indirect DE.now-cong       = reflexive
  direct→indirect (DE.later-cong p) = later-cong (direct→indirect′ p)
  direct→indirect (DE.laterˡ p)     = laterˡ (direct→indirect p)

  direct→indirect′ : ∀ {i x y} →
                     DE.∞Expansion i x y → [ i ] x ≳′ y
  force (direct→indirect′ p) = direct→indirect (force p)

-- If x makes a sequence of zero or more silent transitions to y, then
-- x is an expansion of y.

⇒→≳ : ∀ {i x y} → x ⇒ y → DE.Expansion i x y
⇒→≳ done               = DE.reflexive _
⇒→≳ (step _ later⟶ tr) = DE.laterˡ (⇒→≳ tr)
⇒→≳ (step () now⟶ tr)

-- If x makes a non-silent transition with the label y, then x is an
-- expansion of now y.

[just]⟶→≳now : ∀ {i x x′ y} →
               x [ just y ]⟶ x′ → DE.Expansion i x (now y)
[just]⟶→≳now now⟶ = DE.reflexive _

[just]⇒→≳now : ∀ {i x x′ y} →
               x [ just y ]⇒ x′ → DE.Expansion i x (now y)
[just]⇒→≳now (steps tr now⟶ _) = ⇒→≳ tr

[just]⇒̂→≳now : ∀ {i x x′ y} →
               x [ just y ]⇒̂ x′ → DE.Expansion i x (now y)
[just]⇒̂→≳now (silent () _)
[just]⇒̂→≳now (non-silent _ tr) = [just]⇒→≳now tr

[just]⟶̂→≳now : ∀ {i x x′ y} →
               x [ just y ]⟶̂ x′ → DE.Expansion i x (now y)
[just]⟶̂→≳now (done ())
[just]⟶̂→≳now (step tr) = [just]⇒̂→≳now (⟶→⇒̂ tr)

mutual

  -- The definition of expansion obtained from the transition relation
  -- is contained in the direct one.

  indirect→direct : ∀ {i} x y → [ i ] x ≳ y → DE.Expansion i x y
  indirect→direct {i} (now x) y =
    ([ i ] now x ≳ y)                                ↝⟨ (λ p → left-to-right p now⟶) ⟩
    (∃ λ y′ → y [ just x ]⟶̂ y′ × [ i ] now x ≳′ y′)  ↝⟨ sym ∘ [just]⟶̂→≡now ∘ proj₁ ∘ proj₂ ⟩
    now x ≡ y                                        ↝⟨ (λ { refl → DE.reflexive _ }) ⟩□
    DE.Expansion i (now x) y                         □

  indirect→direct {i} x (now y) =
    [ i ] x ≳ now y                                  ↝⟨ (λ p → right-to-left p now⟶) ⟩
    (∃ λ x′ → x [ just y ]⇒̂ x′ × [ i ] x′ ≳′ now y)  ↝⟨ [just]⇒̂→≳now ∘ proj₁ ∘ proj₂ ⟩□
    DE.Expansion i x (now y)                     □

  indirect→direct (later x) (later y) lx≳ly with left-to-right lx≳ly later⟶
  ... | _ , step later⟶ , x≳′y  = DE.later-cong (∞indirect→direct x≳′y)
  ... | _ , done _      , x≳′ly with right-to-left lx≳ly later⟶
  ...   | _  , non-silent contradiction _ , _     = ⊥-elim (contradiction _)
  ...   | x′ , silent _ (step _ later⟶ x⇒x′) , x′≳′y = DE.later-cong $
                                                       ∞indirect→direct′ x⇒x′ x′≳′y
  ...   | _  , silent _ done                 , lx≳′y = DE.later-cong $
                                                       DE.∞laterˡʳ⁻¹
                                                         (∞indirect→direct lx≳′y)
                                                         (∞indirect→direct x≳′ly)

  -- Lemmas used by indirect→direct.

  indirect→direct′ : ∀ {i x x′ y} →
                     x ⇒ x′ → [ i ] x′ ≳ y → DE.Expansion i x y
  indirect→direct′ done               p = indirect→direct _ _ p
  indirect→direct′ (step _ later⟶ tr) p = DE.laterˡ (indirect→direct′ tr p)
  indirect→direct′ (step () now⟶ _)

  ∞indirect→direct′ : ∀ {i x x′ y} →
                      x ⇒ x′ → [ i ] x′ ≳′ y → DE.∞Expansion i x y
  force (∞indirect→direct′ tr p) = indirect→direct′ tr (force p)

  ∞indirect→direct : ∀ {i x y} →
                     [ i ] x ≳′ y → DE.∞Expansion i x y
  force (∞indirect→direct p) = indirect→direct _ _ (force p)

-- The direct definition of the expansion relation is logically
-- equivalent to the one obtained from the transition relation.
--
-- TODO: Are the two definitions isomorphic?

direct⇔indirect : ∀ {i x y} → DE.Expansion i x y ⇔ [ i ] x ≳ y
direct⇔indirect = record
  { to   = direct→indirect
  ; from = indirect→direct _ _
  }

------------------------------------------------------------------------
-- Some non-existence results

Laterˡ⁻¹′ = ∀ {x} →
            later (record { force = now x }) ≳
            later (record { force = now x }) →
            now x ≳ later (record { force = now x })

laterˡ⁻¹′⇔uninhabited : Laterˡ⁻¹′ ⇔ ¬ A
laterˡ⁻¹′⇔uninhabited =
  Laterˡ⁻¹′     ↝⟨ inverse $ implicit-∀-cong _ $ →-cong _ direct⇔indirect direct⇔indirect ⟩
  DE.Laterˡ⁻¹′  ↝⟨ DE.laterˡ⁻¹′⇔uninhabited ⟩□
  ¬ A           □

Laterˡ⁻¹ = ∀ {x y} → later x ≳ y → force x ≳ y

laterˡ⁻¹⇔uninhabited : Laterˡ⁻¹ ⇔ ¬ A
laterˡ⁻¹⇔uninhabited =
  Laterˡ⁻¹     ↝⟨ inverse $ implicit-∀-cong _ $ implicit-∀-cong _ $ →-cong _ direct⇔indirect direct⇔indirect ⟩
  DE.Laterˡ⁻¹  ↝⟨ DE.laterˡ⁻¹⇔uninhabited ⟩□
  ¬ A          □

Laterʳ⁻¹-∼≳ =
  ∀ {i x} →
  [ i ] never ∼ later (record { force = now x }) →
  [ i ] never ≳ now x

size-preserving-laterʳ⁻¹-∼≳⇔uninhabited : Laterʳ⁻¹-∼≳ ⇔ ¬ A
size-preserving-laterʳ⁻¹-∼≳⇔uninhabited =
  Laterʳ⁻¹-∼≳     ↝⟨ inverse $ implicit-∀-cong _ $ implicit-∀-cong _ $ →-cong _ SD.direct⇔indirect direct⇔indirect ⟩
  DE.Laterʳ⁻¹-∼≳  ↝⟨ DE.size-preserving-laterʳ⁻¹-∼≳⇔uninhabited ⟩□
  ¬ A             □

Laterʳ⁻¹ = ∀ {i x y} → [ i ] x ≳ later y → [ i ] x ≳ force y

size-preserving-laterʳ⁻¹⇔uninhabited : Laterʳ⁻¹ ⇔ ¬ A
size-preserving-laterʳ⁻¹⇔uninhabited =
  Laterʳ⁻¹     ↝⟨ inverse $ implicit-∀-cong _ $ implicit-∀-cong _ $ implicit-∀-cong _ $ →-cong _ direct⇔indirect direct⇔indirect ⟩
  DE.Laterʳ⁻¹  ↝⟨ DE.size-preserving-laterʳ⁻¹⇔uninhabited ⟩□
  ¬ A          □

Transitivity-∼≳ˡ =
  ∀ {i} {x y z : Delay A ∞} →
  [ i ] x ∼ y → y ≳ z → [ i ] x ≳ z

size-preserving-transitivity-∼≳ˡ⇔uninhabited : Transitivity-∼≳ˡ ⇔ ¬ A
size-preserving-transitivity-∼≳ˡ⇔uninhabited =
  Transitivity-∼≳ˡ     ↝⟨ inverse $ implicit-∀-cong _ $ implicit-∀-cong _ $ implicit-∀-cong _ $ implicit-∀-cong _ $
                          →-cong _ SD.direct⇔indirect (→-cong _ direct⇔indirect direct⇔indirect) ⟩
  DE.Transitivity-∼≳ˡ  ↝⟨ DE.size-preserving-transitivity-∼≳ˡ⇔uninhabited ⟩□
  ¬ A                  □

Transitivityˡ =
  ∀ {i} {x y z : Delay A ∞} →
  [ i ] x ≳ y → y ≳ z → [ i ] x ≳ z

size-preserving-transitivityˡ⇔uninhabited : Transitivityˡ ⇔ ¬ A
size-preserving-transitivityˡ⇔uninhabited =
  Transitivityˡ     ↝⟨ inverse $ implicit-∀-cong _ $ implicit-∀-cong _ $ implicit-∀-cong _ $ implicit-∀-cong _ $
                       →-cong _ direct⇔indirect (→-cong _ direct⇔indirect direct⇔indirect) ⟩
  DE.Transitivityˡ  ↝⟨ DE.size-preserving-transitivityˡ⇔uninhabited ⟩□
  ¬ A               □
