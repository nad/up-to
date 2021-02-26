------------------------------------------------------------------------
-- Overloaded "equational" reasoning combinators
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Equational-reasoning where

open import Equality.Propositional
open import Prelude

infix  -1 _■
          finally₁ finally₁∽ finally₁→ finally₁←
          finally₂ finally₂∽ finally₂→ finally₂←
          finally₁-≡∼ finally₁-≡∽ finally₁-≡→ finally₁-≡←
          finally₂-≡∼ finally₂-≡∽ finally₂-≡→ finally₂-≡←
infixr -2 step-⟨⟩∼ step-≡∼ step-≡→ step-∼ step-∼→ step-∼′ step-∼→′
infixl -2 step-⟨⟩∽ step-≡∽ step-≡← step-∽ step-∼← step-∽′ step-∼←′

------------------------------------------------------------------------
-- Reflexivity

record Reflexive {a p} {A : Type a}
                 (P : A → A → Type p) :
                 Type (a ⊔ p) where
  constructor is-reflexive
  field
    reflexive : ∀ {x} → P x x

open Reflexive ⦃ … ⦄ public

_■ : ∀ {a p} {A : Type a} {P : A → A → Type p} ⦃ r : Reflexive P ⦄
     (x : A) → P x x
_ ■ = reflexive

-- Transitivity-like combinators. These combinators can be used when
-- two arguments are definitionally equal. (The Reflexive instance
-- argument is used to make type inference easier.)

step-⟨⟩∼ step-⟨⟩∽ :
  ∀ {a p} {A : Type a} {P : A → A → Type p}
    ⦃ p : Reflexive P ⦄ x {y} →
  P x y → P x y
step-⟨⟩∼ _ p = p
step-⟨⟩∽     = step-⟨⟩∼

syntax step-⟨⟩∼ x Pxy = x ∼⟨⟩ Pxy
syntax step-⟨⟩∽ x Pxy = Pxy ∽⟨⟩ x

-- Transitivity-like combinators. These combinators can be used when
-- two arguments are propositionally equal. (The Reflexive instance
-- argument is used to make type inference easier.)

-- It can be easier for Agda to type-check typical "equational"
-- reasoning chains if the transitivity proof gets the equality
-- arguments in the opposite order, because then the y argument is
-- (perhaps more) known once the proof of P x y is type-checked.
--
-- This optimisation can be quite effective for some examples, but did
-- not seem to have much effect when I applied it to the current code
-- base.
--
-- The idea behind this optimisation came up in discussions with Ulf
-- Norell.

step-≡∼ step-≡∽ step-≡→ step-≡← :
  ∀ {a p} {A : Type a} {P : A → A → Type p}
    ⦃ r : Reflexive P ⦄ x {y z} →
  P y z → x ≡ y → P x z
step-≡∼ _ p refl = p
step-≡∽          = step-≡∼
step-≡→          = step-≡∼
step-≡←          = step-≡∼

syntax step-≡∼ x Pyz x≡y = x ∼≡⟨ x≡y ⟩ Pyz
syntax step-≡∽ x Pyz x≡y = Pyz ∽≡⟨ x≡y ⟩ x
syntax step-≡→ x Pyz x≡y = x →≡⟨ x≡y ⟩ Pyz
syntax step-≡← x Pyz x≡y = Pyz ←≡⟨ x≡y ⟩ x

finally₂-≡∼ finally₂-≡∽ finally₂-≡→ finally₂-≡← :
  ∀ {a p} {A : Type a}
    {P : A → A → Type p}
    ⦃ r : Reflexive P ⦄ x y →
  x ≡ y → P x y
finally₂-≡∼ _ _ refl = reflexive
finally₂-≡∽          = finally₂-≡∼
finally₂-≡→          = finally₂-≡∼
finally₂-≡←          = finally₂-≡∼

syntax finally₂-≡∼ x y x≡y = x ∼≡⟨ x≡y ⟩■ y
syntax finally₂-≡∽ x y x≡y = y ∽≡⟨ x≡y ⟩■ x
syntax finally₂-≡→ x y x≡y = x →≡⟨ x≡y ⟩■ y
syntax finally₂-≡← x y x≡y = y ←≡⟨ x≡y ⟩■ x

finally₁-≡∼ finally₁-≡∽ finally₁-≡→ finally₁-≡← :
  ∀ {a p} {A : Type a}
    {P : A → A → Type p}
    ⦃ r : Reflexive P ⦄ x {y} →
  x ≡ y → P x y
finally₁-≡∼ _ refl = reflexive
finally₁-≡∽        = finally₁-≡∼
finally₁-≡→        = finally₁-≡∼
finally₁-≡←        = finally₁-≡∼

syntax finally₁-≡∼ x x≡y = x ∼≡⟨ x≡y ⟩■
syntax finally₁-≡∽ x x≡y = ∽≡⟨ x≡y ⟩■ x
syntax finally₁-≡→ x x≡y = x →≡⟨ x≡y ⟩■
syntax finally₁-≡← x x≡y = ←≡⟨ x≡y ⟩■ x

------------------------------------------------------------------------
-- Symmetry

record Symmetric {a p} {A : Type a}
                 (P : A → A → Type p) :
                 Type (a ⊔ p) where
  constructor is-symmetric
  field
    symmetric : ∀ {x y} → P x y → P y x

open Symmetric ⦃ … ⦄ public

------------------------------------------------------------------------
-- Transitivity

-- One variant of transitivity.
--
-- Note that the combinator can (depending on the available instances)
-- be used to convert from one type to another, but only in its first
-- argument (in order to make instance resolution easier).

record Transitive {a b p q} {A : Type a} {B : Type b}
                  (P : A → A → Type p) (Q : A → B → Type q) :
                  Type (a ⊔ b ⊔ p ⊔ q) where
  constructor is-transitive
  field
    transitive : ∀ {x y z} → P x y → Q y z → Q x z

open Transitive ⦃ … ⦄ public

step-∼ step-∽ step-∼→ step-∼← :
  ∀ {a b p q} {A : Type a} {B : Type b}
    {P : A → A → Type p} {Q : A → B → Type q}
    ⦃ t : Transitive P Q ⦄ x {y z} →
  Q y z → P x y → Q x z
step-∼ _ = flip transitive
step-∽   = step-∼
step-∼→  = step-∼
step-∼←  = step-∼

syntax step-∼  x Qyz Pxy = x ∼⟨ Pxy ⟩ Qyz
syntax step-∽  x Qyz Pxy = Qyz ∽⟨ Pxy ⟩ x
syntax step-∼→ x Qyz Pxy = x →⟨ Pxy ⟩ Qyz
syntax step-∼← x Qyz Pxy = Qyz ←⟨ Pxy ⟩ x

-- Another variant of transitivity.
--
-- Note that the combinator can (depending on the available instances)
-- be used to convert from one type to another, but only in its second
-- argument (in order to make instance resolution easier).

record Transitive′ {a b p q} {A : Type a} {B : Type b}
                   (P : A → B → Type p) (Q : B → B → Type q) :
                   Type (a ⊔ b ⊔ p ⊔ q) where
  constructor is-transitive
  field
    transitive′ : ∀ {x y z} → P x y → Q y z → P x z

open Transitive′ ⦃ … ⦄ public

step-∼′ step-∽′ step-∼→′ step-∼←′ :
  ∀ {a b p q} {A : Type a} {B : Type b}
    {P : A → B → Type p} {Q : B → B → Type q}
    ⦃ t : Transitive′ P Q ⦄ x {y z} →
  Q y z → P x y → P x z
step-∼′ _ = flip transitive′
step-∽′   = step-∼′
step-∼→′  = step-∼′
step-∼←′  = step-∼′

syntax step-∼′  x Qyz Pxy = x ∼′⟨ Pxy ⟩ Qyz
syntax step-∽′  x Qyz Pxy = Qyz ∽′⟨ Pxy ⟩ x
syntax step-∼→′ x Qyz Pxy = x →′⟨ Pxy ⟩ Qyz
syntax step-∼←′ x Qyz Pxy = Qyz ←′⟨ Pxy ⟩ x

------------------------------------------------------------------------
-- A finally combinator

-- This combinator is intended to be used in the last step of an
-- equational reasoning proof:
--
--   x  ∼⟨ ? ⟩■
--   y
--
-- Note that the combinator can (depending on the available instances)
-- be used to convert from one type to another.

record Convertible {a b p q} {A : Type a} {B : Type b}
                   (P : A → B → Type p) (Q : A → B → Type q) :
                   Type (a ⊔ b ⊔ p ⊔ q) where
  constructor is-convertible
  field
    convert : ∀ {x y} → P x y → Q x y

open Convertible ⦃ … ⦄ public

finally₂ finally₂∽ finally₂→ finally₂← :
  ∀ {a b p q} {A : Type a} {B : Type b}
    {P : A → B → Type p} {Q : A → B → Type q}
    ⦃ c : Convertible P Q ⦄ x y →
  P x y → Q x y
finally₂ _ _ = convert
finally₂∽    = finally₂
finally₂→    = finally₂
finally₂←    = finally₂

syntax finally₂  x y x∼y = x ∼⟨ x∼y ⟩■ y
syntax finally₂∽ x y x∼y = y ∽⟨ x∼y ⟩■ x
syntax finally₂→ x y x→y = x →⟨ x→y ⟩■ y
syntax finally₂← x y x→y = y ←⟨ x→y ⟩■ x

finally₁ finally₁∽ finally₁→ finally₁← :
  ∀ {a b p q} {A : Type a} {B : Type b}
    {P : A → B → Type p} {Q : A → B → Type q}
    ⦃ c : Convertible P Q ⦄ x {y} →
  P x y → Q x y
finally₁ _ = convert
finally₁∽  = finally₁
finally₁→  = finally₁
finally₁←  = finally₁

syntax finally₁  x x∼y = x ∼⟨ x∼y ⟩■
syntax finally₁∽ x x∼y = ∽⟨ x∼y ⟩■ x
syntax finally₁→ x x→y = x →⟨ x→y ⟩■
syntax finally₁← x x→y = ←⟨ x→y ⟩■ x
