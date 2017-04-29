------------------------------------------------------------------------
-- A comparison of the two definitions of bisimilarity
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

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

import Bisimilarity.Classical
import Bisimilarity.Classical.Equational-reasoning-instances
import Bisimilarity.Coinductive
import Bisimilarity.Coinductive.Equational-reasoning-instances
open import Equational-reasoning
open import Labelled-transition-system

module _ {lts : LTS} where

  open LTS lts

  private
    module Cl = Bisimilarity.Classical   lts
    module Co = Bisimilarity.Coinductive lts

  -- Classically bisimilar processes are coinductively bisimilar.

  cl⇒co : ∀ {ℓ i p q} → Cl.[ ℓ ] p ∼ q → Co.[ i ] p ∼ q
  cl⇒co (_R_ , R-is-a-bisimulation , pRq) =
    Co.⟨ (λ p⟶p′ →
            let q′ , q⟶q′ , p′Rq′ =
                  Cl.left-to-right
                    R-is-a-bisimulation pRq p⟶p′
            in q′ , q⟶q′ , cl⇒co′ (_R_ , R-is-a-bisimulation , p′Rq′))
       , (λ q⟶q′ →
            let r′ , r⟶r′ , p′Rq′ =
                  Cl.right-to-left
                    R-is-a-bisimulation pRq q⟶q′
            in r′ , r⟶r′ , cl⇒co′ (_R_ , R-is-a-bisimulation , p′Rq′))
       ⟩
    where
    cl⇒co′ : ∀ {ℓ i p q} → Cl.[ ℓ ] p ∼ q → Co.[ i ] p ∼′ q
    Co.force (cl⇒co′ p∼q) = cl⇒co p∼q

  -- Coinductive bisimilarity is a bisimulation.

  coinductive-bisimilarity-is-a-bisimulation :
    Cl.Bisimulation Co._∼_
  coinductive-bisimilarity-is-a-bisimulation =
    Cl.⟪ (λ p∼q p⟶p′ →
            Σ-map id (Σ-map id (λ p∼q → Co.force p∼q))
              (Co.left-to-right p∼q p⟶p′))
       ,  (λ p∼q q⟶q′ →
            Σ-map id (Σ-map id (λ p∼q → Co.force p∼q))
              (Co.right-to-left p∼q q⟶q′))
       ⟫

  -- Coinductively bisimilar processes are classically bisimilar.

  co⇒cl : ∀ {ℓ p q} → p Co.∼ q → Cl.[ ℓ ] p ∼ q
  co⇒cl p∼q =
      (λ p q → ↑ _ (p Co.∼ q))
    , Cl.↑-preserves-bisimulations
        coinductive-bisimilarity-is-a-bisimulation
    , lift p∼q

  -- The function cl⇒co is a left inverse of co⇒cl.

  cl⇒co∘co⇒cl : ∀ {ℓ i p q}
                (p∼q : p Co.∼ q) →
                Co.[ i ] cl⇒co (co⇒cl {ℓ = ℓ} p∼q) ≡ p∼q
  cl⇒co∘co⇒cl {ℓ} {i} {p} {q} p∼q =
    Co.Bisimilarity-of-∼.⟨ cl⇒co (co⇒cl p∼q)
                         , p∼q
                         , (λ p⟶p′ → refl , refl , lemma₁ p⟶p′)
                         , (λ q⟶q′ → refl , refl , lemma₂ q⟶q′)
                         ⟩
    where
    lemma₁ :
      ∀ {p′ μ} (p⟶p′ : p [ μ ]⟶ p′) →
      Co.[ i ] proj₂ (proj₂ (Co.left-to-right
                               (cl⇒co (co⇒cl {ℓ = ℓ} p∼q)) p⟶p′)) ≡′
               proj₂ (proj₂ (Co.left-to-right p∼q p⟶p′))
    Co.force (lemma₁ p⟶p′) =
      cl⇒co∘co⇒cl (Co.force (proj₂ (proj₂ (Co.left-to-right p∼q p⟶p′))))

    lemma₂ :
      ∀ {q′ μ} (q⟶q′ : q [ μ ]⟶ q′) →
      Co.[ i ] proj₂ (proj₂ (Co.right-to-left
                               (cl⇒co (co⇒cl {ℓ = ℓ} p∼q)) q⟶q′)) ≡′
               proj₂ (proj₂ (Co.right-to-left p∼q q⟶q′))
    Co.force (lemma₂ q⟶q′) =
      cl⇒co∘co⇒cl (Co.force (proj₂ (proj₂ (Co.right-to-left p∼q q⟶q′))))

  -- If there are two processes that are not equal, but bisimilar,
  -- then co⇒cl is not a left inverse of cl⇒co.

  co⇒cl∘cl⇒co : ∀ {p q ℓ} →
                p ≢ q → p Co.∼ q →
                ∃ λ (p∼p : Cl.[ ℓ ] p ∼ p) → co⇒cl (cl⇒co p∼p) ≢ p∼p
  co⇒cl∘cl⇒co {p} {q} p≢q p∼q =
      reflexive

    , (co⇒cl (cl⇒co reflexive) ≡ reflexive  ↝⟨ cong (λ R → proj₁ R p q) ⟩
       ↑ _ (p Co.∼ q) ≡ ↑ _ (p ≡ q)         ↝⟨ (λ eq → ≡⇒↝ _ eq $ lift p∼q) ⟩
       ↑ _ (p ≡ q)                          ↝⟨ lower ⟩
       p ≡ q                                ↝⟨ p≢q ⟩□
       ⊥                                    □)

  -- The two definitions of bisimilarity are logically equivalent.

  classical⇔coinductive :
    ∀ {ℓ p q} → Cl.[ ℓ ] p ∼ q ⇔ p Co.∼ q
  classical⇔coinductive = record
    { to   = cl⇒co
    ; from = co⇒cl
    }

  -- The larger classical versions of bisimilarity are logically
  -- equivalent to the smallest one.

  larger⇔smallest : ∀ {ℓ p q} → Cl.[ ℓ ] p ∼ q ⇔ p Cl.∼ q
  larger⇔smallest {ℓ} {p} {q} =
    Cl.[ ℓ ] p ∼ q  ↝⟨ classical⇔coinductive ⟩
    p Co.∼ q        ↝⟨ inverse classical⇔coinductive ⟩□
    p Cl.∼ q        □

  -- There is a split surjection from the classical definition of
  -- bisimilarity to the coinductive one (assuming extensionality).

  classical↠coinductive :
    Co.Extensionality →
    ∀ {ℓ p q} → Cl.[ ℓ ] p ∼ q ↠ p Co.∼ q
  classical↠coinductive ext = record
    { logical-equivalence = classical⇔coinductive
    ; right-inverse-of    = Co.extensionality ext ∘ cl⇒co∘co⇒cl
    }

-- There is at least one LTS for which there is a split surjection
-- from the coinductive definition of bisimilarity to the classical
-- one.

coinductive↠classical :
  ∀ {ℓ p q} →
  Bisimilarity.Coinductive._∼_  empty   p q ↠
  Bisimilarity.Classical.[_]_∼_ empty ℓ p q
coinductive↠classical {p = ()}

-- There is an LTS for which coinductive bisimilarity is pointwise
-- propositional (assuming extensionality).

coinductive-bisimilarity-is-sometimes-propositional :
  let module Co = Bisimilarity.Coinductive one-loop in
  Co.Extensionality → Is-proposition (tt Co.∼ tt)
coinductive-bisimilarity-is-sometimes-propositional ext =
  _⇔_.from propositional⇔irrelevant λ ∼₁ ∼₂ →
    extensionality ext (irr ∼₁ ∼₂)
  where
  open Bisimilarity.Coinductive one-loop

  irr : ∀ {i} ∼₁ ∼₂ → [ i ] ∼₁ ≡ ∼₂
  irr ∼₁ ∼₂ =
    Bisimilarity-of-∼.⟨ ∼₁
                      , ∼₂
                      , (λ _ → refl , refl , irr′ _ _)
                      , (λ _ → refl , refl , irr′ _ _)
                      ⟩
    where
    irr′ : ∀ {i} ∼₁ ∼₂ → [ i ] ∼₁ ≡′ ∼₂
    force (irr′ ∼₁ ∼₂) = irr (force ∼₁) (force ∼₂)

-- However, classical bisimilarity is, for the same LTS, not pointwise
-- propositional.

classical-bisimilarity-is-not-propositional :
  let module Cl = Bisimilarity.Classical one-loop in
  ∀ {ℓ} → ¬ Is-proposition (Cl.[ ℓ ] tt ∼ tt)
classical-bisimilarity-is-not-propositional {ℓ} =
  Is-proposition ([ ℓ ] tt ∼ tt)    ↝⟨ (λ is-prop → _⇔_.to propositional⇔irrelevant is-prop) ⟩
  Proof-irrelevant ([ ℓ ] tt ∼ tt)  ↝⟨ (λ f → f tt∼tt₁ tt∼tt₂) ⟩
  tt∼tt₁ ≡ tt∼tt₂                   ↝⟨ cong (λ R → proj₁ R tt tt) ⟩
  Unit ≡ (Unit ⊎ Unit)              ↝⟨ (λ eq → Fin 1          ↝⟨ inverse Unit↔Fin1 ⟩
                                               Unit           ↝⟨ ≡⇒↝ _ eq ⟩
                                               Unit ⊎ Unit    ↝⟨ Unit↔Fin1 ⊎-cong Unit↔Fin1 ⟩
                                               Fin 1 ⊎ Fin 1  ↝⟨ Fin⊎Fin↔Fin+ 1 1 ⟩□
                                               Fin 2          □) ⟩
  Fin 1 ↔ Fin 2                     ↝⟨ _⇔_.to isomorphic-same-size ⟩
  1 ≡ 2                             ↝⟨ from-⊎ (1 Nat.≟ 2) ⟩□
  ⊥                                 □
  where
  open Bisimilarity.Classical one-loop

  tt∼tt₁ : [ ℓ ] tt ∼ tt
  tt∼tt₁ = reflexive

  tt∼tt₂ : [ ℓ ] tt ∼ tt
  tt∼tt₂ =
    let _R_ , R-is-a-bisimulation , ttRtt = tt∼tt₁ in
      (λ p q → (p R q) ⊎ (p R q))
    , ×2-preserves-bisimulations R-is-a-bisimulation
    , inj₁ ttRtt

  Unit = ↑ _ (tt ≡ tt)

  Unit↔Fin1 =
    Unit     ↝⟨ Bijection.↑↔ ⟩
    tt ≡ tt  ↝⟨ _⇔_.to contractible⇔↔⊤ (mono₁ 0 ⊤-contractible _ _) ⟩
    ⊤        ↝⟨ inverse ⊎-right-identity ⟩□
    Fin 1    □

-- Thus there is, in general, no split surjection from the coinductive
-- definition of bisimilarity to the classical one (assuming
-- extensionality).

¬coinductive↠classical :
  ∀ {ℓ} →
  Bisimilarity.Coinductive.Extensionality one-loop →
  ¬ (∀ {p q} → Bisimilarity.Coinductive._∼_  one-loop   p q ↠
               Bisimilarity.Classical.[_]_∼_ one-loop ℓ p q)
¬coinductive↠classical {ℓ} ext =
  (∀ {p q} → p Co.∼ q ↠ Cl.[ ℓ ] p ∼ q)                              ↝⟨ (λ co↠cl → co↠cl {q = _}) ⟩
  tt Co.∼ tt ↠ Cl.[ ℓ ] tt ∼ tt                                      ↝⟨ (λ co↠cl → H-level.respects-surjection co↠cl 1) ⟩
  (Is-proposition (tt Co.∼ tt) → Is-proposition (Cl.[ ℓ ] tt ∼ tt))  ↝⟨ (_$ coinductive-bisimilarity-is-sometimes-propositional ext) ⟩
  Is-proposition (Cl.[ ℓ ] tt ∼ tt)                                  ↝⟨ classical-bisimilarity-is-not-propositional ⟩□
  ⊥                                                                  □
  where
  module Cl = Bisimilarity.Classical   one-loop
  module Co = Bisimilarity.Coinductive one-loop

-- Note also that coinductive bisimilarity is not always
-- propositional.

coinductive-bisimilarity-is-not-propositional :
  let open Bisimilarity.Coinductive two-bisimilar-processes in
  ¬ (∀ {p q} → Is-proposition (p ∼ q))
coinductive-bisimilarity-is-not-propositional =
  (∀ {p q} → Is-proposition (p ∼ q))            ↝⟨ (λ is-prop → is-prop {p = true} {q = true}) ⟩
  Is-proposition (true ∼ true)                  ↝⟨ _⇔_.to propositional⇔irrelevant ⟩
  Proof-irrelevant (true ∼ true)                ↝⟨ (λ irr → irr _ _) ⟩
  proof true true true ≡ proof false true true  ↝⟨ cong (λ p → proj₁ (left-to-right {p = true} {q = true} p {p′ = true} _)) ⟩
  true ≡ false                                  ↝⟨ Bool.true≢false ⟩□
  ⊥                                             □
  where
  open Bisimilarity.Coinductive two-bisimilar-processes

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
-- from a certain instance of bisimilarity to equality on A.

bisimilarity↠equality :
  {A : Set} →
  let open Bisimilarity.Coinductive (bisimilarity⇔equality A) in
  {p q : A} → p ∼ q ↠ p ≡ q
bisimilarity↠equality {A} = record
  { logical-equivalence = record
    { to   = to
    ; from = from
    }
  ; right-inverse-of = to∘from
  }
  where
  open Bisimilarity.Coinductive (bisimilarity⇔equality A)

  to : ∀ {p q} → p ∼ q → p ≡ q
  to p∼q with left-to-right p∼q (refl , refl)
  ... | _ , (refl , _) , _ = refl

  from : ∀ {p q} → p ≡ q → p ∼ q
  from refl = reflexive

  to∘from : ∀ {p q} (p≡q : p ≡ q) → to (from p≡q) ≡ p≡q
  to∘from refl = refl
