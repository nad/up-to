------------------------------------------------------------------------
-- Some results about various forms of coinductively defined weak
-- bisimilarity for the delay monad
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe --sized-types #-}

open import Prelude

module Bisimilarity.Weak.Delay-monad {a} {A : Type a} where

open import Delay-monad
open import Delay-monad.Bisimilarity as DB using (force)
import Delay-monad.Bisimilarity.Negative as DN
open import Equality.Propositional
open import Logical-equivalence using (_⇔_)
open import Prelude.Size

open import Function-universe equality-with-J hiding (id; _∘_)
open import Function-universe.Size equality-with-J

import Bisimilarity.Delay-monad as SD
import Bisimilarity.Weak.Alternative.Equational-reasoning-instances
import Bisimilarity.Weak.Equational-reasoning-instances
open import Bisimilarity.Weak.Equivalent
open import Equational-reasoning
import Expansion.Delay-monad as ED
open import Labelled-transition-system.Delay-monad A

open import Bisimilarity delay-monad using ([_]_∼_)
open import Bisimilarity.Weak delay-monad
open import Bisimilarity.Weak.Alternative delay-monad as AW
  using (force)
open import Expansion delay-monad as BE using ([_]_≳_; _≳_)

------------------------------------------------------------------------
-- Several definitions of weak bisimilarity are pointwise logically
-- equivalent

-- Emulations of the constructors DW.later, DW.laterˡ and DW.laterʳ.

later-cong : ∀ {i x y} →
             [ i ] force x ≈′ force y → [ i ] later x ≈ later y
later-cong x≈′y =
  ⟨ (λ { later → _ , ⟶→⇒̂ later , x≈′y })
  , (λ { later → _ , ⟶→⇒̂ later , x≈′y })
  ⟩

laterˡ : ∀ {i x y} → [ i ] force x ≈ y → [ i ] later x ≈ y
laterˡ x≈y =
  ⟨ (λ { later → _ , silent _ done , convert {a = a} x≈y })
  , Σ-map id (Σ-map later⇒̂ id) ∘ right-to-left x≈y
  ⟩

laterʳ : ∀ {i x y} → [ i ] x ≈ force y → [ i ] x ≈ later y
laterʳ x≈y =
  ⟨ Σ-map id (Σ-map later⇒̂ id) ∘ left-to-right x≈y
  , (λ { later → _ , silent _ done , convert {a = a} x≈y })
  ⟩

-- The direct definition of weak bisimilarity is contained in the form
-- of weak bisimilarity obtained from the transition relation.

direct→indirect : ∀ {i x y} →
                  DB.[ i ] x ≈ y → [ i ] x ≈ y
direct→indirect DB.now        = reflexive
direct→indirect (DB.later  p) = later-cong λ { .force →
                                  direct→indirect (force p) }
direct→indirect (DB.laterˡ p) = laterˡ (direct→indirect p)
direct→indirect (DB.laterʳ p) = laterʳ (direct→indirect p)

mutual

  -- The definition of weak bisimilarity obtained from the transition
  -- relation is contained in the direct one.

  indirect→direct : ∀ {i} x y → [ i ] x ≈ y → DB.[ i ] x ≈ y
  indirect→direct {i} (now x) y =
    [ i ] now x ≈ y                                  ↝⟨ (λ p → left-to-right p now) ⟩
    (∃ λ y′ → y [ just x ]⇒̂ y′ × [ i ] now x ≈′ y′)  ↝⟨ DB.≳→ ∘ ED.[just]⇒̂→≳now ∘ proj₁ ∘ proj₂ ⟩
    DB.[ i ] y ≈ now x                               ↝⟨ DB.symmetric ⟩□
    DB.[ i ] now x ≈ y                               □

  indirect→direct {i} x (now y) =
    [ i ] x ≈ now y                                  ↝⟨ (λ p → right-to-left p now) ⟩
    (∃ λ x′ → x [ just y ]⇒̂ x′ × [ i ] x′ ≈′ now y)  ↝⟨ DB.≳→ ∘ ED.[just]⇒̂→≳now ∘ proj₁ ∘ proj₂ ⟩□
    DB.[ i ] x ≈ now y                               □

  indirect→direct (later x) (later y) lx≈ly
    with left-to-right lx≈ly later

  ... | y′ , non-silent contradiction _ , _ =
    ⊥-elim (contradiction _)

  ... | y′ , silent _ (step _ later y⇒y′) , x≈′y′ =
    DB.later λ { .force →
      indirect→direct′ y⇒y′ (force x≈′y′) }

  ... | y′ , silent _ done , x≈′ly
    with right-to-left lx≈ly later

  ...   | x′ , non-silent contradiction _ , _ =
    ⊥-elim (contradiction _)

  ...   | x′ , silent _ (step _ later x⇒x′) , x′≈′y =
    DB.later λ { .force →
      DB.symmetric $
      indirect→direct′ x⇒x′ $
      symmetric (force x′≈′y) }

  ...   | x′ , silent _ done , lx≈′y =
    DB.later λ { .force →
      DB.laterˡʳ⁻¹
        (indirect→direct _ _ (force lx≈′y))
        (indirect→direct _ _ (force x≈′ly)) }

  private

    -- A lemma used by indirect→direct.

    indirect→direct′ : ∀ {i x y y′} →
                       y ⇒ y′ → [ i ] x ≈ y′ → DB.[ i ] x ≈ y
    indirect→direct′ done               p = indirect→direct _ _ p
    indirect→direct′ (step _  later tr) p = DB.laterʳ (indirect→direct′ tr p)
    indirect→direct′ (step () now   _)

-- The direct definition of weak bisimilarity is logically equivalent
-- to the one obtained from the transition relation.
--
-- TODO: Are the two definitions isomorphic?

direct⇔indirect : ∀ {i x y} → DB.[ i ] x ≈ y ⇔ [ i ] x ≈ y
direct⇔indirect = record
  { to   = direct→indirect
  ; from = indirect→direct _ _
  }

-- The direct definition of weak bisimilarity is logically equivalent
-- to the alternative, coinductive form of weak bisimilarity obtained
-- from the transition relation. Note that this proof is not
-- size-preserving.

direct⇔alternative : ∀ {x y} → x DB.≈ y ⇔ x AW.≈ y
direct⇔alternative {x} {y} =
  x DB.≈ y  ↝⟨ direct⇔indirect ⟩
  x ≈ y     ↝⟨ inverse alternative⇔ ⟩□
  x AW.≈ y  □

------------------------------------------------------------------------
-- A non-existence result for the alternative, coinductive indirect
-- definition of weak bisimilarity

private

  -- If A is uninhabited, then AW._≈_ is trivial.

  uninhabited→trivial : ¬ A → ∀ x y → x AW.≈ y
  uninhabited→trivial =
    ¬ A                 ↝⟨ DB.uninhabited→trivial ⟩
    (∀ x y → x DB.≈ y)  ↝⟨ ∀-cong _ (λ _ → ∀-cong _ λ _ → _⇔_.to direct⇔alternative) ⟩
    (∀ x y → x AW.≈ y)  □

-- One can define a size-preserving "later-cong" function iff A is
-- uninhabited.

Later-cong =
  ∀ {i x y} →
  AW.[ i ] force x ≈′ force y → AW.[ i ] later x ≈ later y

size-preserving-later-cong⇔uninhabited : Later-cong ⇔ ¬ A
size-preserving-later-cong⇔uninhabited = record
  { to   = Later-cong                ↝⟨ (λ later-cong → now≈never (λ {i} → later-cong {i})) ⟩
           (∀ x → now x AW.≈ never)  ↝⟨ ∀-cong _ (λ _ → _⇔_.from direct⇔alternative) ⟩
           (∀ x → now x DB.≈ never)  ↝⟨ (λ hyp → DB.now≉never ∘ hyp) ⟩□
           ¬ A                       □
  ; from = ¬ A                 ↝⟨ uninhabited→trivial ⟩
           (∀ x y → x AW.≈ y)  ↝⟨ (λ trivial {_ _ _} _ → trivial _ _) ⟩□
           Later-cong          □
  }
  where

  module _ (later-cong : Later-cong) where

    now≈never : ∀ {i} x → AW.[ i ] now x ≈ never
    now≈never x =
      now x                         ∼⟨ ⇒alternative (laterʳ reflexive) ⟩
      later (λ { .force → now x })  ∼⟨ later-cong (λ { .force → now≈never x }) ⟩■
      never

------------------------------------------------------------------------
-- Some non-existence results for the standard indirect definition of
-- weak bisimilarity

-- There is a transitivity proof that takes weak bisimilarity and
-- expansion to expansion iff A is uninhabited.

Transitivity-≈≳≳ = {x y z : Delay A ∞} → x ≈ y → y ≳ z → x ≳ z
Transitivity-≳≈≳ = {x y z : Delay A ∞} → x ≳ y → y ≈ z → x ≳ z

transitive-≈≳≳⇔uninhabited : Transitivity-≈≳≳ ⇔ ¬ A
transitive-≈≳≳⇔uninhabited =
  Transitivity-≈≳≳     ↝⟨ inverse $ implicit-∀-cong _ $ implicit-∀-cong _ $ implicit-∀-cong _ $
                          →-cong _ direct⇔indirect (→-cong _ ED.direct⇔indirect ED.direct⇔indirect) ⟩
  DN.Transitivity-≈≳≳  ↝⟨ DN.transitive-≈≳≳⇔uninhabited ⟩□
  ¬ A                  □

transitive-≳≈≳⇔uninhabited : Transitivity-≳≈≳ ⇔ ¬ A
transitive-≳≈≳⇔uninhabited =
  Transitivity-≳≈≳     ↝⟨ inverse $ implicit-∀-cong _ $ implicit-∀-cong _ $ implicit-∀-cong _ $
                          →-cong _ ED.direct⇔indirect (→-cong _ direct⇔indirect ED.direct⇔indirect) ⟩
  DN.Transitivity-≳≈≳  ↝⟨ DN.transitive-≳≈≳⇔uninhabited ⟩□
  ¬ A                  □

-- There is a transitivity proof that preserves the size of the second
-- argument iff A is uninhabited.

Transitivityʳ =
  ∀ {i} {x y z : Delay A ∞} →
  x ≈ y → [ i ] y ≈ z → [ i ] x ≈ z

size-preserving-transitivityʳ⇔uninhabited : Transitivityʳ ⇔ ¬ A
size-preserving-transitivityʳ⇔uninhabited =
  Transitivityʳ       ↝⟨ inverse $ implicit-∀-size-cong _ $ implicit-∀-cong _ $ implicit-∀-cong _ $ implicit-∀-cong _ $
                         →-cong _ direct⇔indirect $ →-cong _ direct⇔indirect direct⇔indirect ⟩
  DN.Transitivity-≈ʳ  ↝⟨ DN.size-preserving-transitivity-≈ʳ⇔uninhabited ⟩□
  ¬ A                 □

-- There is a transitivity proof that preserves the size of the first
-- argument iff A is uninhabited.

Transitivityˡ =
  ∀ {i} {x y z : Delay A ∞} →
  [ i ] x ≈ y → y ≈ z → [ i ] x ≈ z

size-preserving-transitivityˡ⇔uninhabited : Transitivityˡ ⇔ ¬ A
size-preserving-transitivityˡ⇔uninhabited =
  Transitivityˡ       ↝⟨ inverse $ implicit-∀-size-cong _ $ implicit-∀-cong _ $ implicit-∀-cong _ $ implicit-∀-cong _ $
                         →-cong _ direct⇔indirect $ →-cong _ direct⇔indirect direct⇔indirect ⟩
  DN.Transitivity-≈ˡ  ↝⟨ DN.size-preserving-transitivity-≈ˡ⇔uninhabited ⟩□
  ¬ A                 □

-- There is a transitivity proof that preserves the size of the second
-- argument, a strong bisimilarity, iff A is uninhabited.

Transitivity-≈∼ʳ =
  ∀ {i} {x y z : Delay A ∞} →
  x ≈ y → [ i ] y ∼ z → [ i ] x ≈ z

size-preserving-transitivity-≈∼ʳ⇔uninhabited : Transitivity-≈∼ʳ ⇔ ¬ A
size-preserving-transitivity-≈∼ʳ⇔uninhabited =
  Transitivity-≈∼ʳ     ↝⟨ inverse $ implicit-∀-size-cong _ $ implicit-∀-cong _ $ implicit-∀-cong _ $ implicit-∀-cong _ $
                          →-cong _ direct⇔indirect $ →-cong _ SD.direct⇔indirect direct⇔indirect ⟩
  DN.Transitivity-≈∼ʳ  ↝⟨ DN.size-preserving-transitivity-≈∼ʳ⇔uninhabited ⟩□
  ¬ A                  □

-- There is a transitivity proof that preserves the size of the first
-- argument, a strong bisimilarity, iff A is uninhabited.

Transitivity-∼≈ˡ =
  ∀ {i} {x y z : Delay A ∞} →
  [ i ] x ∼ y → y ≈ z → [ i ] x ≈ z

size-preserving-transitivity-∼≈ˡ⇔uninhabited : Transitivity-∼≈ˡ ⇔ ¬ A
size-preserving-transitivity-∼≈ˡ⇔uninhabited =
  Transitivity-∼≈ˡ     ↝⟨ inverse $ implicit-∀-size-cong _ $ implicit-∀-cong _ $ implicit-∀-cong _ $ implicit-∀-cong _ $
                          →-cong _ SD.direct⇔indirect $ →-cong _ direct⇔indirect direct⇔indirect ⟩
  DN.Transitivity-∼≈ˡ  ↝⟨ DN.size-preserving-transitivity-∼≈ˡ⇔uninhabited ⟩□
  ¬ A                  □

-- There is a transitivity-like proof that preserves the size of the
-- first argument, an expansion, iff A is uninhabited.

Transitivity-≳≈ˡ =
  ∀ {i} {x y z : Delay A ∞} →
  [ i ] x ≳ y → y ≈ z → [ i ] x ≈ z

size-preserving-transitivity-≳≈ˡ⇔uninhabited : Transitivity-≳≈ˡ ⇔ ¬ A
size-preserving-transitivity-≳≈ˡ⇔uninhabited =
  Transitivity-≳≈ˡ     ↝⟨ inverse $ implicit-∀-size-cong _ $ implicit-∀-cong _ $ implicit-∀-cong _ $ implicit-∀-cong _ $
                          →-cong _ ED.direct⇔indirect (→-cong _ direct⇔indirect direct⇔indirect) ⟩
  DN.Transitivity-≳≈ˡ  ↝⟨ DN.size-preserving-transitivity-≳≈ˡ⇔uninhabited ⟩□
  ¬ A                  □

-- There is a transitivity-like proof that takes an expansion as the
-- first argument, and preserves the size of both arguments, iff A is
-- uninhabited.

Transitivity-≳≈ =
  ∀ {i} {x y z : Delay A ∞} →
  [ i ] x ≳ y → [ i ] y ≈ z → [ i ] x ≈ z

size-preserving-transitivity-≳≈⇔uninhabited : Transitivity-≳≈ ⇔ ¬ A
size-preserving-transitivity-≳≈⇔uninhabited =
  Transitivity-≳≈     ↝⟨ inverse $ implicit-∀-size-cong _ $ implicit-∀-cong _ $ implicit-∀-cong _ $ implicit-∀-cong _ $
                         →-cong _ ED.direct⇔indirect (→-cong _ direct⇔indirect direct⇔indirect) ⟩
  DN.Transitivity-≳≈  ↝⟨ DN.size-preserving-transitivity-≳≈⇔uninhabited ⟩□
  ¬ A                 □

-- There is a transitivity-like proof that preserves the size of the
-- second argument, an expansion (with the arguments swapped), iff A
-- is uninhabited.

Transitivity-≈≲ʳ =
  ∀ {i} {x y z : Delay A ∞} →
  x ≈ y → [ i ] z ≳ y → [ i ] x ≈ z

size-preserving-transitivity-≈≲ʳ⇔uninhabited : Transitivity-≈≲ʳ ⇔ ¬ A
size-preserving-transitivity-≈≲ʳ⇔uninhabited =
  Transitivity-≈≲ʳ     ↝⟨ inverse $ implicit-∀-size-cong _ $ implicit-∀-cong _ $ implicit-∀-cong _ $ implicit-∀-cong _ $
                          →-cong _ direct⇔indirect (→-cong _ ED.direct⇔indirect direct⇔indirect) ⟩
  DN.Transitivity-≈≲ʳ  ↝⟨ DN.size-preserving-transitivity-≈≲ʳ⇔uninhabited ⟩□
  ¬ A                  □

-- There is a transitivity-like proof that takes an expansion (with
-- the arguments swapped) as the second argument, and preserves the
-- size of both arguments, iff A is uninhabited.

Transitivity-≈≲ =
  ∀ {i} {x y z : Delay A ∞} →
  [ i ] x ≈ y → [ i ] z ≳ y → [ i ] x ≈ z

size-preserving-transitivity-≈≲⇔uninhabited : Transitivity-≈≲ ⇔ ¬ A
size-preserving-transitivity-≈≲⇔uninhabited =
  Transitivity-≈≲     ↝⟨ inverse $ implicit-∀-size-cong _ $ implicit-∀-cong _ $ implicit-∀-cong _ $ implicit-∀-cong _ $
                         →-cong _ direct⇔indirect (→-cong _ ED.direct⇔indirect direct⇔indirect) ⟩
  DN.Transitivity-≈≲  ↝⟨ DN.size-preserving-transitivity-≈≲⇔uninhabited ⟩□
  ¬ A                 □

-- There is a transitivity-like proof that preserves the size of the
-- first argument, and takes an expansion as the second argument, iff
-- A is uninhabited.

Transitivity-≈≳ˡ =
  ∀ {i} {x y z : Delay A ∞} →
  [ i ] x ≈ y → y ≳ z → [ i ] x ≈ z

size-preserving-transitivity-≈≳ˡ⇔uninhabited : Transitivity-≈≳ˡ ⇔ ¬ A
size-preserving-transitivity-≈≳ˡ⇔uninhabited =
  Transitivity-≈≳ˡ     ↝⟨ inverse $ implicit-∀-size-cong _ $ implicit-∀-cong _ $ implicit-∀-cong _ $ implicit-∀-cong _ $
                          →-cong _ direct⇔indirect (→-cong _ ED.direct⇔indirect direct⇔indirect) ⟩
  DN.Transitivity-≈≳ˡ  ↝⟨ DN.size-preserving-transitivity-≈≳ˡ⇔uninhabited ⟩□
  ¬ A                  □

------------------------------------------------------------------------
-- A non-existence result for both indirect definitions of weak
-- bisimilarity

-- The function ⇒alternative translating from the standard indirect
-- definition of weak bisimilarity to the alternative, coinductive one
-- can be made size-preserving iff A is uninhabited.

size-preserving-⇒alternative⇔uninhabited :
  (∀ {i p q} → [ i ] p ≈ q → AW.[ i ] p ≈ q) ⇔ ¬ A
size-preserving-⇒alternative⇔uninhabited = record
  { to =
      (∀ {i p q} → [ i ] p ≈ q → AW.[ i ] p ≈ q)  ↝⟨ (λ ⇒alternative x≈y y≈z →
                                                        alternative⇒ (transitive {a = a} (⇒alternative x≈y) (⇒alternative y≈z))) ⟩
      Transitivityʳ                               ↝⟨ _⇔_.to size-preserving-transitivityʳ⇔uninhabited ⟩□
      ¬ A                                         □
  ; from =
      ¬ A                                         ↝⟨ uninhabited→trivial ⟩
      (∀ x y → x AW.≈ y)                          ↝⟨ (λ trivial {_ _ _} _ → trivial _ _) ⟩□
      (∀ {i p q} → [ i ] p ≈ q → AW.[ i ] p ≈ q)  □
  }

------------------------------------------------------------------------
-- More lemmas

-- If x and y both make non-silent transitions of the same kind,
-- then they are weakly bisimilar.

⟶-with-equal-labels→≈ :
  ∀ {x x′ y y′ μ} →
  ¬ Silent μ → x [ μ ]⟶ x′ → y [ μ ]⟶ y′ → x ≈ y
⟶-with-equal-labels→≈ _  now   now = reflexive
⟶-with-equal-labels→≈ ¬s later _   = ⊥-elim (¬s _)

[]⇒-with-equal-labels→≈ :
  ∀ {x x′ y y′ μ} →
  ¬ Silent μ → x [ μ ]⇒ x′ → y [ μ ]⇒ y′ → x ≈ y
[]⇒-with-equal-labels→≈
  {x = x} {y = y} ¬s
  (steps {p′ = x′} x⇒x′ x′⟶x″ x″⇒x‴)
  (steps {p′ = y′} y⇒y′ y′⟶y″ y″⇒y‴) =

  x   ∼⟨ direct→indirect (DB.≳→ (ED.⇒→≳ x⇒x′)) ⟩
  x′  ∼⟨ ⟶-with-equal-labels→≈ ¬s x′⟶x″ y′⟶y″ ⟩
  y′  ∼⟨ symmetric (direct→indirect (DB.≳→ (ED.⇒→≳ y⇒y′))) ⟩■
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
