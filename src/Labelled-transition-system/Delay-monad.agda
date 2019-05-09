------------------------------------------------------------------------
-- A labelled transition system for the delay monad
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe --sized-types #-}

module Labelled-transition-system.Delay-monad {a} (A : Set a) where

open import Delay-monad hiding (steps)
open import Equality.Propositional
open import Prelude
open import Prelude.Size

open import Labelled-transition-system

------------------------------------------------------------------------
-- Transitions

infix 4 _[_]⟶_

data _[_]⟶_ : Delay A ∞ → Maybe A → Delay A ∞ → Set a where
  now   : ∀ {x} → now   x [ just x  ]⟶ now   x
  later : ∀ {x} → later x [ nothing ]⟶ force x

delay-monad : LTS a
delay-monad = record
  { Proc      = Delay A ∞
  ; Label     = Maybe A
  ; _[_]⟶_    = _[_]⟶_
  ; is-silent = if_then true else false
  }

open LTS delay-monad public hiding (_[_]⟶_)

------------------------------------------------------------------------
-- Some simple lemmas

-- If now x can make a sequence of silent transitions to y, then y
-- is equal to now x.

now[nothing]⟶ : ∀ {x y} → now x [ nothing ]⟶ y → y ≡ now x
now[nothing]⟶ ()

now⇒ : ∀ {x y} → now x ⇒ y → y ≡ now x
now⇒ done            = refl
now⇒ (step () now _)

now[nothing]⇒ : ∀ {x y} → now x [ nothing ]⇒ y → y ≡ now x
now[nothing]⇒ (steps nx⇒x′ x′⟶x″ x″⇒y)
  rewrite now⇒ nx⇒x′ | now[nothing]⟶ x′⟶x″ = now⇒ x″⇒y

now[nothing]⇒̂ : ∀ {x y} → now x [ nothing ]⇒̂ y → y ≡ now x
now[nothing]⇒̂ (silent _ tr)     = now⇒ tr
now[nothing]⇒̂ (non-silent ¬s _) = ⊥-elim (¬s _)

now[nothing]⟶̂ : ∀ {x y} → now x [ nothing ]⟶̂ y → y ≡ now x
now[nothing]⟶̂ (done _)  = refl
now[nothing]⟶̂ (step tr) = now[nothing]⟶ tr

-- If now x can make a just y-transition, then x is equal to y.

now[just]⟶ : ∀ {x y z} → now x [ just y ]⟶ z → x ≡ y
now[just]⟶ now = refl

now[just]⇒ : ∀ {x y z} → now x [ just y ]⇒ z → x ≡ y
now[just]⇒ (steps tr₁ tr₂ _) =
  now[just]⟶ (subst (_[ _ ]⟶ _) (now⇒ tr₁) tr₂)

now[just]⇒̂ : ∀ {x y z} → now x [ just y ]⇒̂ z → x ≡ y
now[just]⇒̂ (silent () _)
now[just]⇒̂ (non-silent _ tr) = now[just]⇒ tr

now[just]⟶̂ : ∀ {x y z} → now x [ just y ]⟶̂ z → x ≡ y
now[just]⟶̂ (done ())
now[just]⟶̂ (step tr) = now[just]⟶ tr

-- The computation never can only transition to itself.

never⟶never : ∀ {μ x} → never [ μ ]⟶ x → x ≡ never
never⟶never later = refl

never⇒never : ∀ {x} → never ⇒ x → x ≡ never
never⇒never done               = refl
never⇒never (step _ later ne⇒) = never⇒never ne⇒

never[]⇒never : ∀ {μ x} → never [ μ ]⇒ x → x ≡ never
never[]⇒never (steps ne⇒x x⟶y y⇒z)
  rewrite never⇒never ne⇒x | never⟶never x⟶y = never⇒never y⇒z

never⇒̂never : ∀ {μ x} → never [ μ ]⇒̂ x → x ≡ never
never⇒̂never (silent     _ ne⇒) = never⇒never ne⇒
never⇒̂never (non-silent _ ne⇒) = never[]⇒never ne⇒

never⟶̂never : ∀ {μ x} → never [ μ ]⟶̂ x → x ≡ never
never⟶̂never (done _)   = refl
never⟶̂never (step ne⟶) = never⟶never ne⟶

-- If never can make a μ-transition, then μ is silent.

never⟶→silent : ∀ {μ x} → never [ μ ]⟶ x → Silent μ
never⟶→silent later = _

never[]⇒→silent : ∀ {μ x} → never [ μ ]⇒ x → Silent μ
never[]⇒→silent (steps ne⇒x  x⟶  _) with never⇒never ne⇒x
never[]⇒→silent (steps ne⇒ne ne⟶ _) | refl = never⟶→silent ne⟶

never⇒̂→silent : ∀ {μ x} → never [ μ ]⇒̂ x → Silent μ
never⇒̂→silent (silent s _)       = s
never⇒̂→silent (non-silent _ ne⇒) = never[]⇒→silent ne⇒

never⟶̂→silent : ∀ {μ x} → never [ μ ]⟶̂ x → Silent μ
never⟶̂→silent (done s)   = s
never⟶̂→silent (step ne⟶) = never⟶→silent ne⟶

-- If x can make a non-silent transition, with label just y, to z,
-- then z is equal to now y.

[just]⟶ : ∀ {x y z} → x [ just y ]⟶ z → z ≡ now y
[just]⟶ now = refl

[just]⇒ : ∀ {x y z} → x [ just y ]⇒ z → z ≡ now y
[just]⇒ (steps _ now ny⇒z) = now⇒ ny⇒z

[just]⇒̂ : ∀ {x y z} → x [ just y ]⇒̂ z → z ≡ now y
[just]⇒̂ (silent () _)
[just]⇒̂ (non-silent _ x⇒z) = [just]⇒ x⇒z

[just]⟶̂ : ∀ {x y z} → x [ just y ]⟶̂ z → z ≡ now y
[just]⟶̂ (done ())
[just]⟶̂ (step x⟶z) = [just]⟶ x⟶z

-- In some cases x is also equal to now y.

[just]⟶→≡now : ∀ {x y z} → x [ just y ]⟶ z → x ≡ now y
[just]⟶→≡now now = refl

[just]⟶̂→≡now : ∀ {x y z} → x [ just y ]⟶̂ z → x ≡ now y
[just]⟶̂→≡now (done ())
[just]⟶̂→≡now (step x⟶z) = [just]⟶→≡now x⟶z

-- If force x can make a weak μ-transition (_[_]⇒_ or _[_]⇒̂_) to y,
-- then later x can also make a weak μ-transition (of the same kind)
-- to y.

later[]⇒ : ∀ {μ x y} → force x [ μ ]⇒ y → later x [ μ ]⇒ y
later[]⇒ = ⇒[]⇒-transitive (⟶→⇒ _ later)

later⇒̂ : ∀ {μ x y} → force x [ μ ]⇒̂ y → later x [ μ ]⇒̂ y
later⇒̂ = ⇒⇒̂-transitive (⟶→⇒ _ later)

-- The process x can make a silent transition to drop-later x.

⇒drop-later : ∀ {x} → x ⇒ drop-later x
⇒drop-later {now x}   = done
⇒drop-later {later x} = step _ later done

-- If x can make a transition to y, then drop-later x can in some
-- cases make a transition of the same kind to drop-later y.

drop-later-cong⟶ :
  ∀ {x μ y} →
  ¬ Silent μ → x [ μ ]⟶ y → drop-later x [ μ ]⟶ drop-later y
drop-later-cong⟶ _  now   = now
drop-later-cong⟶ ¬s later = ⊥-elim (¬s _)

drop-later-cong⇒ : ∀ {x y} → x ⇒ y → drop-later x ⇒ drop-later y
drop-later-cong⇒ done                = done
drop-later-cong⇒ (step () now   _)
drop-later-cong⇒ (step _  later x⇒y) =
  ⇒-transitive ⇒drop-later (drop-later-cong⇒ x⇒y)

drop-later-cong[]⇒ :
  ∀ {x μ y} →
  ¬ Silent μ → x [ μ ]⇒ y → drop-later x [ μ ]⇒ drop-later y
drop-later-cong[]⇒ ¬s (steps x⇒y y⟶z z⇒u) =
  steps (drop-later-cong⇒ x⇒y) (drop-later-cong⟶ ¬s y⟶z)
        (drop-later-cong⇒ z⇒u)

drop-later-cong⇒̂ :
  ∀ {x μ y} → x [ μ ]⇒̂ y → drop-later x [ μ ]⇒̂ drop-later y
drop-later-cong⇒̂ (silent s x⇒y)      = silent s (drop-later-cong⇒ x⇒y)
drop-later-cong⇒̂ (non-silent ¬s x⇒y) =
  non-silent ¬s (drop-later-cong[]⇒ ¬s x⇒y)

drop-later-cong⟶̂ :
  ∀ {x μ y} →
  ¬ Silent μ → x [ μ ]⟶̂ y → drop-later x [ μ ]⟶̂ drop-later y
drop-later-cong⟶̂ _  (done s)   = done s
drop-later-cong⟶̂ ¬s (step x⟶y) = step (drop-later-cong⟶ ¬s x⟶y)

-- If later x can make a transition to later y, then force x can
-- make a transition (of the same kind) to force y.

drop-later⟶ :
  ∀ {μ x y} → later x [ μ ]⟶ later y → force x [ μ ]⟶ force y
drop-later⟶ lx⟶ly = helper lx⟶ly refl refl
  where
  helper : ∀ {μ x x′ y y′} →
           later x [ μ ]⟶ y′ →
           y′ ≡ later y →
           x′ ≡ force x →
           x′ [ μ ]⟶ force y
  helper {x = x} {x′} {y} later x≡ly x′≡x =
    subst (_[ _ ]⟶ _) ly≡x′ later
    where
    ly≡x′ =
      later y  ≡⟨ sym x≡ly ⟩
      force x  ≡⟨ sym x′≡x ⟩∎
      x′       ∎

drop-later⇒ : ∀ {x y} → later x ⇒ later y → force x ⇒ force y
drop-later⇒ = drop-later-cong⇒

drop-later[]⇒ :
  ∀ {μ x y} → later x [ μ ]⇒ later y → force x [ μ ]⇒ force y
drop-later[]⇒ (steps lx⇒ly later y⇒lz) =
  ⇒[]⇒-transitive (⇒-transitive (drop-later⇒ lx⇒ly) y⇒lz)
                  (⟶→[]⇒ later)
drop-later[]⇒ (steps _ now ny⇒lz) with now⇒ ny⇒lz
... | ()

drop-later⇒̂ :
  ∀ {μ x y} → later x [ μ ]⇒̂ later y → force x [ μ ]⇒̂ force y
drop-later⇒̂ = drop-later-cong⇒̂

drop-later⟶̂ :
  ∀ {μ x y} → later x [ μ ]⟶̂ later y → force x [ μ ]⟶̂ force y
drop-later⟶̂ (done s)     = done s
drop-later⟶̂ (step lx⟶ly) = step (drop-later⟶ lx⟶ly)

-- If x makes silent transitions to both y and z, then one of y and
-- z makes silent transitions to the other.

⇒×⇒→… : ∀ {x y z} → x ⇒ y → x ⇒ z → y ⇒ z ⊎ z ⇒ y
⇒×⇒→… done               x⇒z                = inj₁ x⇒z
⇒×⇒→… x⇒y                done               = inj₂ x⇒y
⇒×⇒→… (step _ later x⇒y) (step _ later x⇒z) = ⇒×⇒→… x⇒y x⇒z
⇒×⇒→… (step () now _)

-- If x makes silent transitions to y and a non-silent weak
-- μ-transition (of one kind) to z, then y makes a weak μ-transition
-- to z.

⇒×⇒[]→… :
  ∀ {x y z μ} →
  ¬ Silent μ → x ⇒ y → x [ μ ]⇒ z → y [ μ ]⇒ z
⇒×⇒[]→… _ x⇒y (steps x⇒x′ x′⟶x″ x″⇒z) with ⇒×⇒→… x⇒y x⇒x′
⇒×⇒[]→… _ _   (steps _    x′⟶x″ x″⇒z) | inj₁ y⇒x′ = steps y⇒x′ x′⟶x″ x″⇒z
⇒×⇒[]→… _ _   (steps _    now   n⇒z)  | inj₂ done = steps done now   n⇒z

⇒×⇒[]→… _  _  _                 | inj₂ (step () now _)
⇒×⇒[]→… ¬s _  (steps _ later _) | _ = ⊥-elim (¬s _)

-- If x makes silent transitions to y and a weak μ-transition (of
-- one kind) to z, then either y makes a weak μ-transition to z, or
-- μ is silent and z makes silent transitions to y.

⇒×⇒̂→… :
  ∀ {x y z μ} → x ⇒ y → x [ μ ]⇒̂ z → y [ μ ]⇒̂ z ⊎ Silent μ × z ⇒ y
⇒×⇒̂→… x⇒y (silent     s  x⇒z) = ⊎-map (silent s) (s ,_)
                                      (⇒×⇒→… x⇒y x⇒z)
⇒×⇒̂→… x⇒y (non-silent ¬s x⇒z) =
  inj₁ (non-silent ¬s (⇒×⇒[]→… ¬s x⇒y x⇒z))
