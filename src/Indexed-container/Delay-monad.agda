------------------------------------------------------------------------
-- The delay monad defined as the greatest fixpoint of an indexed
-- container
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe --sized-types #-}

module Indexed-container.Delay-monad where

open import Equality.Propositional as E using (_≡_; refl)
open import Logical-equivalence using (_⇔_)
open import Prelude
open import Prelude.Size

open import Bijection E.equality-with-J as Bijection using (_↔_)
open import Function-universe E.equality-with-J as F hiding (_∘_)

open import Delay-monad
open import Delay-monad.Bisimilarity as B

open import Indexed-container
open import Indexed-container.Combinators as C hiding (_∘_)
open import Relation

-- A container for the delay monad.

DelayC : ∀ {ℓ} → Set ℓ → Container (↑ ℓ ⊤) (↑ ℓ ⊤)
DelayC A =
  (λ _ → Maybe A) ◁ λ { (just _) _ → ⊥; nothing _ → ↑ _ ⊤ }

-- An alternative definition.

DelayC′ : ∀ {ℓ} → Set ℓ → Container (↑ ℓ ⊤) (↑ ℓ ⊤)
DelayC′ A = C.id ⊕ C.const (λ _ → A)

-- The two containers' interpretations are pointwise logically
-- equivalent, and in the presence of extensionality they are
-- pointwise isomorphic.

⟦DelayC⟧↔⟦DelayC′⟧ :
  ∀ {k a x} {A : Set a} {X : Rel x (↑ a ⊤)} {i} →
  Extensionality? k a (a ⊔ x) →
  ⟦ DelayC A ⟧ X i ↝[ k ] ⟦ DelayC′ A ⟧ X i
⟦DelayC⟧↔⟦DelayC′⟧ {k} {a} {A = A} {X} {i} ext =
  ⟦ DelayC A ⟧ X i                                              ↔⟨⟩
  (∃ λ (s : Maybe A) → Container.Position (DelayC A) s ⊆ X)     ↝⟨ Σ-cong (inverse Bijection.↑↔ ⊎-cong F.id)
                                                                     [ (λ _ → implicit-∀-cong ext $
                                                                              Π-cong (lower-extensionality? k lzero a ext) lemma λ _ →
                                                                              F.id)
                                                                     , (λ _ → F.id)
                                                                     ] ⟩
  (∃ λ (s : ↑ _ ⊤ ⊎ A) → [ (λ _ → _ ≡_) , (λ _ _ → ⊥) ] s ⊆ X)  ↔⟨⟩
  ⟦ DelayC′ A ⟧ X i                                             □
  where
  lemma : ↑ a ⊤ ↔ lift {ℓ = a} tt ≡ lift tt
  lemma = record
    { surjection = record
      { logical-equivalence = record
        { to = λ _ → refl
        }
      ; right-inverse-of = λ { refl → refl }
      }
    ; left-inverse-of = λ _ → refl
    }

-- An unfolding lemma.

νDelayC↔ : ∀ {k a i} {A : Set a} →
           Extensionality? k a a →
           ν (DelayC A) i _ ↝[ k ] A ⊎ ν′ (DelayC A) i _
νDelayC↔ {i = i} {A} ext =
  ν (DelayC A) i _                           ↔⟨⟩

  ⟦ DelayC  A ⟧ (ν′ (DelayC A) i) _          ↝⟨ ⟦DelayC⟧↔⟦DelayC′⟧ ext ⟩

  ⟦ DelayC′ A ⟧ (ν′ (DelayC A) i) _          ↔⟨ ⟦⊕⟧↔ C.id (C.const (λ _ → A)) ⟩

  ⟦ C.id ⟧ (ν′ (DelayC A) i) _ ⊎
  ⟦ C.const (λ _ → A) ⟧ (ν′ (DelayC A) i) _  ↝⟨ ⟦id⟧↔ ext ⊎-cong ⟦const⟧↔ _ ext ⟩

  ν′ (DelayC A) i _ ⊎ A                      ↔⟨ ⊎-comm ⟩□

  A ⊎ ν′ (DelayC A) i _                      □

-- There is a (size-preserving) logical equivalence between the direct
-- definition of the delay monad and an indirect definition using the
-- container DelayC and ν.

mutual

  Delay⇔νDelayC : ∀ {a i} {A : Set a} → Delay A i ⇔ ν (DelayC A) i _
  Delay⇔νDelayC {i = i} {A} =
    Delay A i              ↔⟨ Delay↔ ⟩
    A ⊎ Delay′ A i         ↝⟨ F.id ⊎-cong Delay′⇔ν′DelayC ⟩
    A ⊎ ν′ (DelayC A) i _  ↝⟨ inverse $ νDelayC↔ _ ⟩□
    ν (DelayC A) i _       □

  Delay′⇔ν′DelayC : ∀ {a i} {A : Set a} → Delay′ A i ⇔ ν′ (DelayC A) i _
  Delay′⇔ν′DelayC = record
    { to   = λ x → λ { .force → _⇔_.to   Delay⇔νDelayC (force x) }
    ; from = λ x → λ { .force → _⇔_.from Delay⇔νDelayC (force x) }
    }

-- The two components of Delay⇔νDelayC {i = ∞} are inverses up to
-- (strong) bisimilarity.

Delay⇔νDelayC-inverses :
  ∀ {a} {A : Set a} →
  let to   = _⇔_.to   (Delay⇔νDelayC {i = ∞})
      from = _⇔_.from (Delay⇔νDelayC {i = ∞})
  in
  (∀ x → ν-bisimilar ∞ (to (from x) , x))
    ×
  (∀ x → [ ∞ ] from (to x) ∼ x)
Delay⇔νDelayC-inverses {A = A} = to∘from , from∘to
  where
  to : ∀ {i} → Delay A i → ν (DelayC A) i _
  to = _⇔_.to Delay⇔νDelayC

  from : ∀ {i} → ν (DelayC A) i _ → Delay A i
  from = _⇔_.from Delay⇔νDelayC

  abstract

    from∘to : ∀ {i} x → [ i ] from (to x) ∼ x
    from∘to (now x)   = now x ∎
    from∘to (later x) = later λ { .force →
      from (to (force x))  ∼⟨ from∘to (force x) ⟩∼
      force x              ∎ }

    to∘from : ∀ {i} x → ν-bisimilar i (to (from x) , x)
    to∘from x@(just _ , _) =
      _⇔_.from (ν-bisimilar↔ _ (to (from x)) x)
        ( refl
        , λ ()
        )
    to∘from x@(nothing , f) =
      _⇔_.from (ν-bisimilar↔ _ (to (from x)) x)
        ( refl
        , λ p → λ { .force → to∘from (force (f p)) }
        )

-- There is an isomorphism between the direct definition of the delay
-- monad and an indirect definition using the container DelayC and ν
-- (assuming three kinds of extensionality).

Delay↔νDelayC :
  ∀ {a} {A : Set a} →
  E.Extensionality a a →
  B.Extensionality a →
  ν′-extensionality (DelayC A) →
  Delay A ∞ ↔ ν (DelayC A) ∞ _
Delay↔νDelayC ext ∼-ext ν′-ext = record
  { surjection = record
    { logical-equivalence = Delay⇔νDelayC
    ; right-inverse-of    = ν-extensionality ext ν′-ext ∘
                            proj₁ Delay⇔νDelayC-inverses
    }
  ; left-inverse-of = ∼-ext ∘ proj₂ Delay⇔νDelayC-inverses
  }
