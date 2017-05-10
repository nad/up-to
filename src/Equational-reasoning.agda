------------------------------------------------------------------------
-- Overloaded "equational" reasoning combinators
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Equational-reasoning where

open import Prelude

infix  -1 _■ finally₁ finally₁→ finally₁← finally₂ finally₂→ finally₂←
infixr -2 step-∼ step-∼→ _∼⟨⟩_ step-∽ step-∽→
infixl -2 step-∼← step-∽←

------------------------------------------------------------------------
-- Reflexivity

record Reflexive {a p} {A : Set a}
                 (P : A → A → Set p) :
                 Set (a ⊔ p) where
  constructor is-reflexive
  field
    reflexive : ∀ {x} → P x x

open Reflexive ⦃ … ⦄ public

_■ : ∀ {a p} {A : Set a} {P : A → A → Set p} ⦃ r : Reflexive P ⦄
     (x : A) → P x x
_ ■ = reflexive

-- A transitivity-like combinator. This combinator can be used when
-- two arguments are definitionally equal. (The Reflexive instance
-- argument is used to make type inference easier.)

_∼⟨⟩_ : ∀ {a p} {A : Set a} {P : A → A → Set p}
          ⦃ p : Reflexive P ⦄ x {y} →
        P x y → P x y
_ ∼⟨⟩ p = p

------------------------------------------------------------------------
-- Symmetry

record Symmetric {a p} {A : Set a}
                 (P : A → A → Set p) :
                 Set (a ⊔ p) where
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

record Transitive {a b p q} {A : Set a} {B : Set b}
                  (P : A → A → Set p) (Q : A → B → Set q) :
                  Set (a ⊔ b ⊔ p ⊔ q) where
  constructor is-transitive
  field
    transitive : ∀ {x y z} → P x y → Q y z → Q x z

open Transitive ⦃ … ⦄ public

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

step-∼ step-∼→ step-∼← :
  ∀ {a b p q} {A : Set a} {B : Set b}
    {P : A → A → Set p} {Q : A → B → Set q}
    ⦃ t : Transitive P Q ⦄ x {y z} →
  Q y z → P x y → Q x z
step-∼ _ = flip transitive
step-∼→  = step-∼
step-∼←  = step-∼

syntax step-∼  x Qyz Pxy = x ∼⟨ Pxy ⟩ Qyz
syntax step-∼→ x Qyz Pxy = x →⟨ Pxy ⟩ Qyz
syntax step-∼← x Qyz Pxy = Qyz ←⟨ Pxy ⟩ x

-- Another variant of transitivity.
--
-- Note that the combinator can (depending on the available instances)
-- be used to convert from one type to another, but only in its second
-- argument (in order to make instance resolution easier).

record Transitive′ {a b p q} {A : Set a} {B : Set b}
                   (P : A → B → Set p) (Q : B → B → Set q) :
                   Set (a ⊔ b ⊔ p ⊔ q) where
  constructor is-transitive
  field
    transitive′ : ∀ {x y z} → P x y → Q y z → P x z

open Transitive′ ⦃ … ⦄ public

step-∽ step-∽→ step-∽← :
  ∀ {a b p q} {A : Set a} {B : Set b}
    {P : A → B → Set p} {Q : B → B → Set q}
    ⦃ t : Transitive′ P Q ⦄ x {y z} →
  Q y z → P x y → P x z
step-∽ _ = flip transitive′
step-∽→  = step-∽
step-∽←  = step-∽

syntax step-∽  x Qyz Pxy = x ∽⟨ Pxy ⟩ Qyz
syntax step-∽→ x Qyz Pxy = x →∽⟨ Pxy ⟩ Qyz
syntax step-∽← x Qyz Pxy = Qyz ←∽⟨ Pxy ⟩ x

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

record Convertible {a b p q} {A : Set a} {B : Set b}
                   (P : A → B → Set p) (Q : A → B → Set q) :
                   Set (a ⊔ b ⊔ p ⊔ q) where
  constructor is-convertible
  field
    convert : ∀ {x y} → P x y → Q x y

open Convertible ⦃ … ⦄ public

finally₂ finally₂→ finally₂← :
  ∀ {a b p q} {A : Set a} {B : Set b}
    {P : A → B → Set p} {Q : A → B → Set q}
    ⦃ c : Convertible P Q ⦄ x y →
  P x y → Q x y
finally₂ _ _ = convert
finally₂→    = finally₂
finally₂←    = finally₂

syntax finally₂  x y x∼y = x ∼⟨ x∼y ⟩■ y
syntax finally₂→ x y x→y = x →⟨ x→y ⟩■ y
syntax finally₂← x y x→y = y ←⟨ x→y ⟩■ x

finally₁ finally₁→ finally₁← :
  ∀ {a b p q} {A : Set a} {B : Set b}
    {P : A → B → Set p} {Q : A → B → Set q}
    ⦃ c : Convertible P Q ⦄ x {y} →
  P x y → Q x y
finally₁ _ = convert
finally₁→  = finally₁
finally₁←  = finally₁

syntax finally₁  x x∼y = x ∼⟨ x∼y ⟩■
syntax finally₁→ x x→y = x →⟨ x→y ⟩■
syntax finally₁← x x→y = ←⟨ x→y ⟩■ x
