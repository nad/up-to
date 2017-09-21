------------------------------------------------------------------------
-- Some counterexamples
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Bisimilarity.Up-to.Counterexamples where

open import Equality.Propositional
open import Logical-equivalence using (_⇔_)
open import Prelude

open import Bijection equality-with-J using (_↔_)
open import Equality.Decision-procedures equality-with-J
open import Fin equality-with-J
open import Function-universe equality-with-J hiding (id; _∘_)
open import Surjection equality-with-J using (_↠_)

open import Indexed-container using (Container; ν; ⟦_⟧; force)
open import Labelled-transition-system
import Up-to

import Bisimilarity.Classical
import Bisimilarity.Coinductive
import Bisimilarity.Coinductive.Equational-reasoning-instances
open import Bisimilarity.Comparison
import Bisimilarity.Step
import Bisimilarity.Up-to
open import Equational-reasoning
open import Relation

private

  -- A combination of some parametrised modules.

  module Combination (lts : LTS) where

    open Bisimilarity.Classical lts public
      using (Progression)
    open Bisimilarity.Coinductive lts public
    open Bisimilarity.Step lts (LTS._[_]⟶_ lts) (LTS._[_]⟶_ lts) public
      using (Step; Step↔S̲t̲e̲p̲)
    open Bisimilarity.Up-to lts public
    open LTS lts public hiding (_[_]⟶_)

-- Size-preserving relation transformers are not necessarily monotone
-- or extensive.

¬size-preserving→monotone⊎extensive :
  ∃ λ lts → let open Combination lts in
  ¬ ((F : Trans₂ (# 0) Proc) → Size-preserving F →
     Monotone F ⊎ Extensive F)
¬size-preserving→monotone⊎extensive =
    one-loop
  , ((∀ G → Size-preserving G → Monotone G ⊎ Extensive G)  ↝⟨ (λ hyp → hyp _ F-pres) ⟩
     Monotone F ⊎ Extensive F                              ↝⟨ [ ¬-F-mono , ¬-F-extensive ] ⟩□
     ⊥                                                     □)
  where
  open Combination one-loop

  F : Trans₂ (# 0) Proc
  F R = ¬_ ∘ R

  ¬-F-mono : ¬ Monotone F
  ¬-F-mono =
    Monotone F                                                   ↝⟨ (λ mono → mono {_}) ⟩
    ((λ _ → ⊥) ⊆ (λ _ → ↑ _ ⊤) → F (λ _ → ⊥) ⊆ F (λ _ → ↑ _ ⊤))  ↔⟨⟩
    ((λ _ → ⊥) ⊆ (λ _ → ↑ _ ⊤) → (λ _ → ¬ ⊥) ⊆ (λ _ → ¬ ↑ _ ⊤))  ↝⟨ _$ _ ⟩
    (λ _ → ¬ ⊥) ⊆ (λ _ → ¬ ↑ _ ⊤)                                ↝⟨ (λ hyp → hyp {tt}) ⟩
    (¬ ⊥ → ¬ ↑ _ ⊤)                                              ↝⟨ _$ ⊥-elim ⟩
    ¬ ↑ _ ⊤                                                      ↝⟨ _$ _ ⟩□
    ⊥                                                            □

  ¬-F-extensive : ¬ Extensive F
  ¬-F-extensive =
    Extensive F        ↝⟨ (λ hyp → hyp _) ⟩
    (↑ _ ⊤ → ¬ ↑ _ ⊤)  ↝⟨ (_$ _) ∘ (_$ _) ⟩□
    ⊥                  □

  total : ∀ {i x y} → [ i ] x ∼ y
  total = reflexive

  F-pres : Size-preserving F
  F-pres _ _ = total

-- Relation transformers F that satisfy ∀ {i} → F (ν C i) ⊆ ν C i are
-- not necessarily up-to techniques.

¬special-case-of-size-preserving→up-to :
  ∃ λ (I : Set) →
  ∃ λ (C : Container I I) →
  ¬ ((F : Trans (# 0) I) →
     (∀ {i} → F (ν C i) ⊆ ν C i) → Up-to.Up-to-technique C F)
¬special-case-of-size-preserving→up-to =
    (Proc × Proc)
  , S̲t̲e̲p̲
  , ((∀ F → (∀ {i} → F (Bisimilarity i) ⊆ Bisimilarity i) →
      Up-to-technique F)                                                  ↝⟨ _$ G ⟩

     ((∀ {i} → G (Bisimilarity i) ⊆ Bisimilarity i) → Up-to-technique G)  ↝⟨ _$ bisimilarity-pre-fixpoint ⟩

     Up-to-technique G                                                    ↝⟨ (λ up-to → up-to) ⟩

     (S ⊆ ⟦ S̲t̲e̲p̲ ⟧ (G S) → S ⊆ Bisimilarity ∞)                            ↝⟨ (λ hyp below → hyp (Step↔S̲t̲e̲p̲ _ ∘ below)) ⟩

     (S ⊆ Step (G S) → S ⊆ Bisimilarity ∞)                                ↝⟨ _$ S⊆StepGS ⟩

     S ⊆ Bisimilarity ∞                                                   ↝⟨ _$ pq ⟩

     Bisimilarity ∞ (p , q)                                               ↝⟨ p≁q ⟩□

     ⊥                                                                    □)

  where

  data Proc : Set where
    p q r : Proc

  data _⟶_ : Proc → Proc → Set where
    p : p ⟶ p
    q : q ⟶ r

  lts = record
    { Proc    = Proc
    ; Label   = ⊤
    ; Silent  = λ _ → ⊥
    ; silent? = λ _ → no λ ()
    ; _[_]⟶_  = λ p _ q → p ⟶ q
    }

  open Combination lts hiding (Proc)

  G : Trans₂ (# 0) Proc
  G R x = R (r , r) → ¬ R (p , r) → R x

  p≁r : ∀ {i} → ¬ Bisimilarity i (p , r)
  p≁r hyp with left-to-right hyp p
  ... | _ , () , _

  bisimilarity-pre-fixpoint :
    ∀ {i} → G (Bisimilarity i) ⊆ Bisimilarity i
  bisimilarity-pre-fixpoint hyp = hyp reflexive p≁r

  data S : Rel₂ (# 0) Proc where
    pq : S (p , q)

  S⊆StepGS : S ⊆ Step (G S)
  Step.left-to-right (S⊆StepGS pq) p = r , q , λ ()
  Step.right-to-left (S⊆StepGS pq) q = p , p , λ ()

  p≁q : ¬ Bisimilarity ∞ (p , q)
  p≁q hyp with left-to-right hyp p
  ... | r , q , p∼r = p≁r (force p∼r)

-- Relation transformers F that satisfy ∀ {i} → F (ν C i) ⊆ ν C i are
-- not necessarily size-preserving.

¬special-case-of-size-preserving→size-preserving :
  ∃ λ (I : Set) →
  ∃ λ (C : Container I I) →
  ¬ ((F : Trans (# 0) I) →
     (∀ {i} → F (ν C i) ⊆ ν C i) → Up-to.Size-preserving C F)
¬special-case-of-size-preserving→size-preserving =
  case ¬special-case-of-size-preserving→up-to of λ where
    (I , C , ¬→up-to) →
      let open Up-to C in
        I , C
      , (((F : Trans (# 0) I) →
          (∀ {i} → F (ν C i) ⊆ ν C i) → Up-to.Size-preserving C F)  ↝⟨ (λ hyp F pres → size-preserving→up-to (hyp F pres)) ⟩

         ((F : Trans (# 0) I) →
          (∀ {i} → F (ν C i) ⊆ ν C i) → Up-to.Up-to-technique C F)  ↝⟨ ¬→up-to ⟩□

         ⊥                                                          □)

-- Monotone, extensive, size-preserving relation transformers are not
-- necessarily compatible.

¬monotone→extensive→size-preserving→compatible :
  ∃ λ lts → let open Combination lts in
  ¬ ((F : Trans₂ (# 0) Proc) →
     Monotone F → Extensive F → Size-preserving F → Compatible F)
¬monotone→extensive→size-preserving→compatible =
    one-transition

  , ((∀ F → Monotone F → Extensive F → Size-preserving F → Compatible F)  ↝⟨ (λ hyp → hyp F mono extensive
                                                                                        (_⇔_.from (monotone→⇔ mono) (λ {_ x} → pre {x = x}))) ⟩
     Compatible F                                                         ↝⟨ ¬comp ⟩□
     ⊥                                                                    □)

  where

  -- An LTS with two distinct processes and one transition from one to
  -- the other.

  one-transition : LTS
  one-transition = record
    { Proc    = Bool
    ; Label   = ⊤
    ; Silent  = λ _ → ⊥
    ; silent? = λ _ → no λ ()
    ; _[_]⟶_  = λ x _ y → T (x ∧ not y)
    }

  open Combination one-transition

  -- A relation transformer.

  F : Trans₂ (# 0) Proc
  F R (true , true) = R (false , false) ⊎ R (true , true)
  F R               = R

  -- F is monotone.

  mono : Monotone F
  mono R⊆S {true  , true}  = ⊎-map R⊆S R⊆S
  mono R⊆S {true  , false} = R⊆S
  mono R⊆S {false , true}  = R⊆S
  mono R⊆S {false , false} = R⊆S

  -- F is extensive.

  extensive : Extensive F
  extensive R {true  , true}  = inj₂
  extensive R {true  , false} = id
  extensive R {false , true}  = id
  extensive R {false , false} = id

  -- Bisimilarity of size i is a pre-fixpoint of F.

  pre : ∀ {i} → F (Bisimilarity i) ⊆ Bisimilarity i
  pre {x = true  , true}  = λ _ → true ■
  pre {x = true  , false} = id
  pre {x = false , true}  = id
  pre {x = false , false} = id

  -- A relation.

  R : Rel₂ (# 0) Proc
  R _ = ⊥

  -- A lemma.

  StepRff : Step R (false , false)
  Step.left-to-right StepRff ()
  Step.right-to-left StepRff ()

  -- F is not compatible.

  ¬comp : ¬ Compatible F
  ¬comp =
    Compatible F                                                   ↝⟨ (λ comp {x} → comp R {x}) ⟩

    F (⟦ S̲t̲e̲p̲ ⟧ R) ⊆ ⟦ S̲t̲e̲p̲ ⟧ (F R)                                ↝⟨ (λ le → le {true , true}) ⟩

    (F (⟦ S̲t̲e̲p̲ ⟧ R) (true , true) → ⟦ S̲t̲e̲p̲ ⟧ (F R) (true , true))  ↔⟨⟩

    (⟦ S̲t̲e̲p̲ ⟧ R (false , false) ⊎ ⟦ S̲t̲e̲p̲ ⟧ R (true , true) →
     ⟦ S̲t̲e̲p̲ ⟧ (F R) (true , true))                                 ↝⟨ _$ inj₁ (_⇔_.to (Step↔S̲t̲e̲p̲ _) StepRff) ⟩

    ⟦ S̲t̲e̲p̲ ⟧ (F R) (true , true)                                   ↝⟨ (λ step → S̲t̲e̲p̲.left-to-right {p = true} {q = true} step {p′ = false} _ ) ⟩

    (∃ λ y → T (not y) × F R (false , y))                          ↔⟨⟩

    (∃ λ y → T (not y) × ⊥)                                        ↝⟨ proj₂ ∘ proj₂ ⟩□

    ⊥                                                              □

-- Up-to-technique is not closed under composition, not even for
-- monotone and extensive relation transformers.
--
-- (Pous and Sangiorgi discuss another counterexample to this property
-- in Section 6.5.4 of "Enhancements of the bisimulation proof
-- method".)

¬-∘-closure :
  ∃ λ lts → let open Combination lts in
  ¬ ({F G : Trans₂ (# 0) Proc} →
     Monotone F → Extensive F →
     Monotone G → Extensive G →
     Up-to-technique F →
     Up-to-technique G →
     Up-to-technique (F ∘ G))
¬-∘-closure =
    lts

  , ((∀ {F G} →
      Monotone F → Extensive F → Monotone G → Extensive G →
      Up-to-technique F → Up-to-technique G → Up-to-technique (F ∘ G))  ↝⟨ (λ cl → cl F-lemmas.mono F-lemmas.ext G-lemmas.mono G-lemmas.ext
                                                                                      F-lemmas.up-to G-lemmas.up-to) ⟩

     Up-to-technique (F ∘ G)                                            ↝⟨ (λ up-to → up-to R̲-prog′) ⟩

     R̲ ⊆ Bisimilarity ∞                                                 ↝⟨ (λ le → le pp) ⟩

     p left ∼ p right                                                   ↝⟨ (λ rel → S̲t̲e̲p̲.left-to-right rel pq) ⟩

     (∃ λ y → p right [ pq ]⟶ y × q left ∼′ y)                          ↝⟨ (λ { (.(q right) , pq , rel) → rel }) ⟩

     q left ∼′ q right                                                  ↝⟨ (λ rel → S̲t̲e̲p̲.left-to-right (force rel) qq) ⟩

     (∃ λ y → q right [ qq left ]⟶ y × q left ∼′ y)                     ↝⟨ (λ { (_ , () , _) }) ⟩□

     ⊥                                                                  □)

  where

  ----------------------------------------------------------------------
  -- An LTS with two sets of processes, three "to the left", and three
  -- "to the right"

  Side : Set
  Side = Bool

  pattern left  = true
  pattern right = false

  data Process : Set where
    p q r : Side → Process

  data Label : Set where
    pq pr : Label
    qq rr : Side → Label

  infix 4 _[_]⟶_

  data _[_]⟶_ : Process → Label → Process → Set where
    pq : ∀ {s} → p s [ pq ]⟶ q s
    pr : ∀ {s} → p s [ pr ]⟶ r s
    qq : ∀ {s} → q s [ qq s ]⟶ q s
    rr : ∀ {s} → r s [ rr s ]⟶ r s

  lts : LTS
  lts = record
    { Proc    = Process
    ; Label   = Label
    ; Silent  = λ _ → ⊥
    ; silent? = λ _ → no λ ()
    ; _[_]⟶_  = _[_]⟶_
    }

  open Combination lts

  ----------------------------------------------------------------------
  -- Two relation transformers and one relation

  -- F and G both add (at most) one pair to the underlying relation.

  data F (R : Rel₂ (# 0) Proc) : Rel₂ (# 0) Proc where
    qq  : F R (q left , q right)
    [_] : ∀ {x} → R x → F R x

  data G (R : Rel₂ (# 0) Proc) : Rel₂ (# 0) Proc where
    rr  : G R (r left , r right)
    [_] : ∀ {x} → R x → G R x

  -- R̲ adds one pair to reflexivity.

  data R̲ : Rel₂ (# 0) Proc where
    pp   : R̲ (p left , p right)
    refl : ∀ {x} → R̲ (x , x)

  -- R̲ progresses to F (G R̲).

  R̲-prog : Progression R̲ (F (G R̲))
  R̲-prog pp   = Step.⟨ (λ where
                          pq → _ , pq , qq
                          pr → _ , pr , [ rr ])
                     , (λ where
                          pq → _ , pq , qq
                          pr → _ , pr , [ rr ])
                     ⟩
  R̲-prog refl = Step.⟨ (λ where
                          pq → _ , pq , [ [ refl ] ]
                          pr → _ , pr , [ [ refl ] ]
                          qq → _ , qq , [ [ refl ] ]
                          rr → _ , rr , [ [ refl ] ])
                     , (λ where
                          pq → _ , pq , [ [ refl ] ]
                          pr → _ , pr , [ [ refl ] ]
                          qq → _ , qq , [ [ refl ] ]
                          rr → _ , rr , [ [ refl ] ])
                     ⟩

  R̲-prog′ : R̲ ⊆ ⟦ S̲t̲e̲p̲ ⟧ (F (G R̲))
  R̲-prog′ Rx = _⇔_.to (Step↔S̲t̲e̲p̲ _) (R̲-prog Rx)

  module F-lemmas where

    -- F is monotone.

    mono : Monotone F
    mono R⊆S qq      = qq
    mono R⊆S [ Rxy ] = [ R⊆S Rxy ]

    -- F is extensive.

    ext : Extensive F
    ext = λ _ → [_]

    -- F is an up-to technique.

    module _ {R} (R-prog′ : R ⊆ ⟦ S̲t̲e̲p̲ ⟧ (F R)) where

      R-prog : Progression R (F R)
      R-prog Rx = _⇔_.from (Step↔S̲t̲e̲p̲ _) (R-prog′ Rx)

      ¬rr : ∀ {s} → ¬ R (r s , r (not s))
      ¬rr rel with Progression.left-to-right R-prog rel rr
      ¬rr {true}  _ | _ , () , _
      ¬rr {false} _ | _ , () , _

      ¬qq : ∀ {s} → ¬ R (q s , q (not s))
      ¬qq rel with Progression.left-to-right R-prog rel qq
      ¬qq {true}  _ | _ , () , _
      ¬qq {false} _ | _ , () , _

      ¬pp : ∀ {s} → ¬ R (p s , p (not s))
      ¬pp rel with Progression.left-to-right R-prog rel pr
      ... | .(r _) , pr , [ rel′ ] = ¬rr rel′

      ¬pq : ∀ {s₁ s₂} → ¬ R (p s₁ , q s₂)
      ¬pq rel with Progression.left-to-right R-prog rel pq
      ... | _ , () , _

      ¬qp : ∀ {s₁ s₂} → ¬ R (q s₁ , p s₂)
      ¬qp rel with Progression.right-to-left R-prog rel pq
      ... | _ , () , _

      ¬pr : ∀ {s₁ s₂} → ¬ R (p s₁ , r s₂)
      ¬pr rel with Progression.left-to-right R-prog rel pq
      ... | _ , () , _

      ¬rp : ∀ {s₁ s₂} → ¬ R (r s₁ , p s₂)
      ¬rp rel with Progression.right-to-left R-prog rel pq
      ... | _ , () , _

      ¬qr : ∀ {s₁ s₂} → ¬ R (q s₁ , r s₂)
      ¬qr rel with Progression.right-to-left R-prog rel rr
      ... | _ , () , _

      ¬rq : ∀ {s₁ s₂} → ¬ R (r s₁ , q s₂)
      ¬rq rel with Progression.left-to-right R-prog rel rr
      ... | _ , () , _

      up-to : R ⊆ Bisimilarity ∞
      up-to {p left  , p left}  rel = reflexive
      up-to {p left  , p right} rel = ⊥-elim (¬pp rel)
      up-to {p right , p left}  rel = ⊥-elim (¬pp rel)
      up-to {p right , p right} rel = reflexive
      up-to {p _     , q _}     rel = ⊥-elim (¬pq rel)
      up-to {p _     , r _}     rel = ⊥-elim (¬pr rel)
      up-to {q _     , p _}     rel = ⊥-elim (¬qp rel)
      up-to {q left  , q left}  rel = reflexive
      up-to {q left  , q right} rel = ⊥-elim (¬qq rel)
      up-to {q right , q left}  rel = ⊥-elim (¬qq rel)
      up-to {q right , q right} rel = reflexive
      up-to {q _     , r _}     rel = ⊥-elim (¬qr rel)
      up-to {r _     , p _}     rel = ⊥-elim (¬rp rel)
      up-to {r _     , q _}     rel = ⊥-elim (¬rq rel)
      up-to {r left  , r left}  rel = reflexive
      up-to {r left  , r right} rel = ⊥-elim (¬rr rel)
      up-to {r right , r left}  rel = ⊥-elim (¬rr rel)
      up-to {r right , r right} rel = reflexive

  module G-lemmas where

    -- G is monotone.

    mono : Monotone G
    mono R⊆S rr      = rr
    mono R⊆S [ Rxy ] = [ R⊆S Rxy ]

    -- G is extensive.

    ext : Extensive G
    ext = λ _ → [_]

    -- G is an up-to technique.

    module _ {R} (R-prog′ : R ⊆ ⟦ S̲t̲e̲p̲ ⟧ (G R)) where

      R-prog : Progression R (G R)
      R-prog Rx = _⇔_.from (Step↔S̲t̲e̲p̲ _) (R-prog′ Rx)

      ¬rr : ∀ {s} → ¬ R (r s , r (not s))
      ¬rr rel with Progression.left-to-right R-prog rel rr
      ¬rr {true}  _ | _ , () , _
      ¬rr {false} _ | _ , () , _

      ¬qq : ∀ {s} → ¬ R (q s , q (not s))
      ¬qq rel with Progression.left-to-right R-prog rel qq
      ¬qq {true}  _ | _ , () , _
      ¬qq {false} _ | _ , () , _

      ¬pp : ∀ {s} → ¬ R (p s , p (not s))
      ¬pp rel with Progression.left-to-right R-prog rel pq
      ... | .(q _) , pq , [ rel′ ] = ¬qq rel′

      ¬pq : ∀ {s₁ s₂} → ¬ R (p s₁ , q s₂)
      ¬pq rel with Progression.left-to-right R-prog rel pq
      ... | _ , () , _

      ¬qp : ∀ {s₁ s₂} → ¬ R (q s₁ , p s₂)
      ¬qp rel with Progression.right-to-left R-prog rel pq
      ... | _ , () , _

      ¬pr : ∀ {s₁ s₂} → ¬ R (p s₁ , r s₂)
      ¬pr rel with Progression.left-to-right R-prog rel pq
      ... | _ , () , _

      ¬rp : ∀ {s₁ s₂} → ¬ R (r s₁ , p s₂)
      ¬rp rel with Progression.right-to-left R-prog rel pq
      ... | _ , () , _

      ¬qr : ∀ {s₁ s₂} → ¬ R (q s₁ , r s₂)
      ¬qr rel with Progression.right-to-left R-prog rel rr
      ... | _ , () , _

      ¬rq : ∀ {s₁ s₂} → ¬ R (r s₁ , q s₂)
      ¬rq rel with Progression.left-to-right R-prog rel rr
      ... | _ , () , _

      up-to : R ⊆ Bisimilarity ∞
      up-to {p left  , p left}  rel = reflexive
      up-to {p left  , p right} rel = ⊥-elim (¬pp rel)
      up-to {p right , p left}  rel = ⊥-elim (¬pp rel)
      up-to {p right , p right} rel = reflexive
      up-to {p _     , q _}     rel = ⊥-elim (¬pq rel)
      up-to {p _     , r _}     rel = ⊥-elim (¬pr rel)
      up-to {q _     , p _}     rel = ⊥-elim (¬qp rel)
      up-to {q left  , q left}  rel = reflexive
      up-to {q left  , q right} rel = ⊥-elim (¬qq rel)
      up-to {q right , q left}  rel = ⊥-elim (¬qq rel)
      up-to {q right , q right} rel = reflexive
      up-to {q _     , r _}     rel = ⊥-elim (¬qr rel)
      up-to {r _     , p _}     rel = ⊥-elim (¬rp rel)
      up-to {r _     , q _}     rel = ⊥-elim (¬rq rel)
      up-to {r left  , r left}  rel = reflexive
      up-to {r left  , r right} rel = ⊥-elim (¬rr rel)
      up-to {r right , r left}  rel = ⊥-elim (¬rr rel)
      up-to {r right , r right} rel = reflexive

-- Up-to techniques are not necessarily size-preserving, not even if
-- they are monotone and extensive.

¬monotone→extensive→up-to→size-preserving :
  ∃ λ lts → let open Combination lts in
  ¬ ((F : Trans₂ (# 0) Proc) →
     Monotone F → Extensive F → Up-to-technique F → Size-preserving F)
¬monotone→extensive→up-to→size-preserving =
  let lts , ¬-∘-closure = ¬-∘-closure
      open Combination lts
  in

    lts

  , λ monotone→extensive→up-to→size-preserving →

    ¬-∘-closure λ {F G} F-mono F-ext G-mono G-ext F-up-to G-up-to →

                                             $⟨ (λ {_ _} → monotone→extensive→up-to→size-preserving F F-mono F-ext F-up-to) ,
                                                (λ {_ _} → monotone→extensive→up-to→size-preserving G G-mono G-ext G-up-to) ⟩

      Size-preserving F × Size-preserving G  ↝⟨ uncurry ∘-closure ⟩

      Size-preserving (F ∘ G)                ↝⟨ size-preserving→up-to ⟩□

      Up-to-technique (F ∘ G)                □
