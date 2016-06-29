------------------------------------------------------------------------
-- Overloaded "equational" reasoning combinators
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Equational-reasoning where

open import Prelude

infix  -1 _■ finally
infixr -2 _∼⟨_⟩_ _∼⟨⟩_ _∽⟨_⟩_

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

_∼⟨_⟩_ : ∀ {a b p q} {A : Set a} {B : Set b}
           {P : A → A → Set p} {Q : A → B → Set q}
           ⦃ t : Transitive P Q ⦄ x {y z} →
         P x y → Q y z → Q x z
_∼⟨_⟩_ _ = transitive

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

_∽⟨_⟩_ : ∀ {a b p q} {A : Set a} {B : Set b}
           {P : A → B → Set p} {Q : B → B → Set q}
           ⦃ t : Transitive′ P Q ⦄ x {y z} →
         P x y → Q y z → P x z
_∽⟨_⟩_ _ = transitive′

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

finally : ∀ {a b p q} {A : Set a} {B : Set b}
            {P : A → B → Set p} {Q : A → B → Set q}
            ⦃ c : Convertible P Q ⦄ x y →
          P x y → Q x y
finally _ _ = convert

syntax finally x y x∼y = x ∼⟨ x∼y ⟩■ y
