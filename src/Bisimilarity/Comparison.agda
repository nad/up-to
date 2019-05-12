------------------------------------------------------------------------
-- A comparison of the two definitions of bisimilarity
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe --sized-types #-}

module Bisimilarity.Comparison where

open import Equality.Propositional
open import Logical-equivalence using (_⇔_)
open import Prelude hiding (Unit)

open import Bijection equality-with-J as Bijection using (_↔_)
open import Equality.Decision-procedures equality-with-J
open import Fin equality-with-J
open import Function-universe equality-with-J hiding (_∘_; id)
open import H-level equality-with-J as H-level
open import H-level.Closure equality-with-J
open import Nat equality-with-J as Nat
open import Surjection equality-with-J using (_↠_)

import Bisimilarity
import Bisimilarity.Classical
import Bisimilarity.Classical.Equational-reasoning-instances
import Bisimilarity.Equational-reasoning-instances
open import Equational-reasoning
import Indexed-container as IC
open import Labelled-transition-system
open import Relation

module _ {ℓ} {lts : LTS ℓ} where

  open LTS lts

  private
    module Cl = Bisimilarity.Classical lts
    module Co = Bisimilarity           lts

  -- Classically bisimilar processes are coinductively bisimilar.

  cl⇒co : ∀ {i p q} → p Cl.∼ q → Co.[ i ] p ∼ q
  cl⇒co = IC.gfp⊆ν ℓ

  -- Coinductively bisimilar processes are classically bisimilar.

  co⇒cl : ∀ {p q} → p Co.∼ q → p Cl.∼ q
  co⇒cl = IC.ν⊆gfp ℓ

  -- The function cl⇒co is a left inverse of co⇒cl (up to pointwise
  -- bisimilarity).

  cl⇒co∘co⇒cl : ∀ {i p q}
                (p∼q : p Co.∼ q) →
                Co.[ i ] cl⇒co (co⇒cl p∼q) ≡ p∼q
  cl⇒co∘co⇒cl p∼q = IC.gfp⊆ν∘ν⊆gfp ℓ p∼q

  -- If there are two processes that are not equal, but bisimilar,
  -- then co⇒cl is not a left inverse of cl⇒co.

  co⇒cl∘cl⇒co : ∀ {p q} →
                p ≢ q → p Co.∼ q →
                ∃ λ (p∼p : p Cl.∼ p) → co⇒cl (cl⇒co p∼p) ≢ p∼p
  co⇒cl∘cl⇒co {p} {q} p≢q p∼q =
      reflexive

    , (co⇒cl (cl⇒co reflexive) ≡ reflexive  ↝⟨ cong (λ R → proj₁ R (p , q)) ⟩
       ↑ _ (p Co.∼ q) ≡ ↑ _ (p ≡ q)         ↝⟨ (λ eq → ≡⇒↝ _ eq $ lift p∼q) ⟩
       ↑ _ (p ≡ q)                          ↔⟨ Bijection.↑↔ ⟩
       p ≡ q                                ↝⟨ p≢q ⟩□
       ⊥                                    □)

  -- The two definitions of bisimilarity are logically equivalent.

  classical⇔coinductive : ∀ {p q} → p Cl.∼ q ⇔ p Co.∼ q
  classical⇔coinductive = IC.gfp⇔ν ℓ

  -- There is a split surjection from the classical definition of
  -- bisimilarity to the coinductive one (assuming two kinds of
  -- extensionality).

  classical↠coinductive :
    Extensionality ℓ ℓ →
    Co.Extensionality →
    ∀ {p q} → p Cl.∼ q ↠ p Co.∼ q
  classical↠coinductive ext co-ext = IC.gfp↠ν ext ℓ co-ext

-- There is at least one LTS for which there is a split surjection
-- from the coinductive definition of bisimilarity to the classical
-- one.

coinductive↠classical :
  ∀ {p q} →
  Bisimilarity._∼_           empty p q ↠
  Bisimilarity.Classical._∼_ empty p q
coinductive↠classical {p = ()}

-- There is an LTS for which coinductive bisimilarity is pointwise
-- propositional (assuming two kinds of extensionality).

coinductive-bisimilarity-is-sometimes-propositional :
  Extensionality lzero lzero →
  let module Co = Bisimilarity one-loop in
  Co.Extensionality → Is-proposition (tt Co.∼ tt)
coinductive-bisimilarity-is-sometimes-propositional ext co-ext ∼₁ ∼₂ =
  extensionality ext co-ext (irr ∼₁ ∼₂)
  where
  open Bisimilarity one-loop

  irr : ∀ {i} ∼₁ ∼₂ → [ i ] ∼₁ ≡ ∼₂
  irr ∼₁ ∼₂ =
    Bisimilarity-of-∼.⟨ ext
                      , ∼₁
                      , ∼₂
                      , (λ _ → refl , refl , irr′ (proj₂ ∼₁ _)
                                                  (proj₂ ∼₂ _))
                      , (λ _ → refl , refl , irr′ (proj₂ ∼₁ _)
                                                  (proj₂ ∼₂ _))
                      ⟩
    where
    irr′ : ∀ {i} ∼₁ ∼₂ → [ i ] ∼₁ ≡′ ∼₂
    force (irr′ ∼₁ ∼₂) = irr (force ∼₁) (force ∼₂)

-- However, classical bisimilarity (of any size) is, for the same LTS,
-- not pointwise propositional.

classical-bisimilarity-is-not-propositional :
  let module Cl = Bisimilarity.Classical one-loop in
  ∀ {ℓ} → ¬ Is-proposition (Cl.Bisimilarity′ ℓ (tt , tt))
classical-bisimilarity-is-not-propositional {ℓ} =
  Is-proposition (Bisimilarity′ ℓ (tt , tt))    ↝⟨ (λ f → f tt∼tt₁ tt∼tt₂) ⟩
  tt∼tt₁ ≡ tt∼tt₂                               ↝⟨ cong (λ R → proj₁ R (tt , tt)) ⟩
  Unit ≡ (Unit ⊎ Unit)                          ↝⟨ (λ eq → Fin 1          ↝⟨ inverse Unit↔Fin1 ⟩
                                                           Unit           ↝⟨ ≡⇒↝ _ eq ⟩
                                                           Unit ⊎ Unit    ↝⟨ Unit↔Fin1 ⊎-cong Unit↔Fin1 ⟩
                                                           Fin 1 ⊎ Fin 1  ↝⟨ Fin⊎Fin↔Fin+ 1 1 ⟩□
                                                           Fin 2          □) ⟩
  Fin 1 ↔ Fin 2                                 ↝⟨ _⇔_.to isomorphic-same-size ⟩
  1 ≡ 2                                         ↝⟨ from-⊎ (1 Nat.≟ 2) ⟩□
  ⊥                                             □
  where
  open Bisimilarity.Classical one-loop

  tt∼tt₁ : Bisimilarity′ ℓ (tt , tt)
  tt∼tt₁ = reflexive-∼′ _

  tt∼tt₂ : Bisimilarity′ ℓ (tt , tt)
  tt∼tt₂ =
    let R , R-is-a-bisimulation , ttRtt =
          _⇔_.to (Bisimilarity′↔ _ _) tt∼tt₁ in
    _⇔_.from (Bisimilarity′↔ _ _)
      ( (R ∪ R)
      , ×2-preserves-bisimulations R-is-a-bisimulation
      , inj₁ ttRtt
      )

  Unit = ↑ ℓ (tt ≡ tt)

  Unit↔Fin1 =
    Unit     ↔⟨ Bijection.↑↔ ⟩
    tt ≡ tt  ↝⟨ _⇔_.to contractible⇔↔⊤ (+⇒≡ $ mono₁ 0 ⊤-contractible) ⟩
    ⊤        ↝⟨ inverse ⊎-right-identity ⟩□
    Fin 1    □

-- Thus, assuming two kinds of extensionality, there is in general no
-- split surjection from the coinductive definition of bisimilarity to
-- the classical one (of any size).

¬coinductive↠classical :
  Extensionality lzero lzero →
  Bisimilarity.Extensionality one-loop →
  ∀ {ℓ} →
  ¬ (∀ {p q} → Bisimilarity._∼_                     one-loop    p   q ↠
               Bisimilarity.Classical.Bisimilarity′ one-loop ℓ (p , q))
¬coinductive↠classical ext co-ext {ℓ} =
  (∀ {p q} → p Co.∼ q ↠ Cl.Bisimilarity′ ℓ (p , q))  ↝⟨ (λ co↠cl → co↠cl {q = _}) ⟩

  tt Co.∼ tt ↠ Cl.Bisimilarity′ ℓ (tt , tt)          ↝⟨ (λ co↠cl → H-level.respects-surjection co↠cl 1) ⟩

  (Is-proposition (tt Co.∼ tt) →
   Is-proposition (Cl.Bisimilarity′ ℓ (tt , tt)))    ↝⟨ (_$ coinductive-bisimilarity-is-sometimes-propositional ext co-ext) ⟩

  Is-proposition (Cl.Bisimilarity′ ℓ (tt , tt))      ↝⟨ classical-bisimilarity-is-not-propositional ⟩□

  ⊥                                                  □
  where
  module Cl = Bisimilarity.Classical one-loop
  module Co = Bisimilarity           one-loop

-- Note also that coinductive bisimilarity is not always
-- propositional.

coinductive-bisimilarity-is-not-propositional :
  let open Bisimilarity two-bisimilar-processes in
  ¬ (∀ {p q} → Is-proposition (p ∼ q))
coinductive-bisimilarity-is-not-propositional =
  (∀ {p q} → Is-proposition (p ∼ q))            ↝⟨ (λ is-prop → is-prop {p = true} {q = true}) ⟩
  Is-proposition (true ∼ true)                  ↝⟨ (λ irr → irr _ _) ⟩
  proof true true true ≡ proof false true true  ↝⟨ cong (λ p → proj₁ (left-to-right {p = true} {q = true} p {p′ = true} _)) ⟩
  true ≡ false                                  ↝⟨ Bool.true≢false ⟩□
  ⊥                                             □
  where
  open Bisimilarity two-bisimilar-processes

  open import Indexed-container

  mutual
    proof : Bool → ∀ b₁ b₂ {i} → [ i ] b₁ ∼ b₂
    proof b b₁ b₂ =
      ⟨_,_⟩ {p = b₁} {q = b₂}
        (λ _ → b , _ , proof′ b _ _)
        (λ _ → b , _ , proof′ b _ _)

    proof′ : Bool → ∀ b₁ b₂ {i} → [ i ] b₁ ∼′ b₂
    force (proof′ b b₁ b₂) = proof b b₁ b₂

-- In fact, for every type A there is a pointwise split surjection
-- from a certain instance of bisimilarity (of any size) to equality
-- on A.

bisimilarity↠equality :
  ∀ {a} {A : Set a} →
  let open Bisimilarity (bisimilarity⇔equality A) in
  ∀ {i} {p q : A} → ([ i ] p ∼ q) ↠ p ≡ q
bisimilarity↠equality {A = A} {i} = record
  { logical-equivalence = record
    { to   = to
    ; from = from
    }
  ; right-inverse-of = to∘from
  }
  where
  open Bisimilarity (bisimilarity⇔equality A)

  to : ∀ {p q} → [ i ] p ∼ q → p ≡ q
  to p∼q with left-to-right p∼q (refl , refl)
  ... | _ , (refl , _) , _ = refl

  from : ∀ {p q} → p ≡ q → [ i ] p ∼ q
  from refl = reflexive

  to∘from : ∀ {p q} (p≡q : p ≡ q) → to (from p≡q) ≡ p≡q
  to∘from refl = refl
