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

  module Combination {ℓ} (lts : LTS ℓ) where

    open Bisimilarity.Classical lts public
      using (Progression)
    open Bisimilarity.Coinductive lts public
    open Bisimilarity.Step lts (LTS._[_]⟶_ lts) (LTS._[_]⟶_ lts) public
      using (Step; Step↔S̲t̲e̲p̲)
    open Bisimilarity.Up-to lts public
    open LTS lts public hiding (_[_]⟶_)

-- There is a size-preserving relation transformer that is neither
-- monotone nor extensive.

∃size-preserving×¬[monotone⊎extensive] :
  ∃ λ (lts : LTS lzero) →
  let open Combination lts in
  ∃ λ (F : Trans₂ (# 0) Proc) →
      Size-preserving F × ¬ (Monotone F ⊎ Extensive F)
∃size-preserving×¬[monotone⊎extensive] =
  one-loop , F , F-pres , [ ¬-F-mono , ¬-F-extensive ]
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

-- There is a relation transformer F satisfying
-- ∀ {i} → F (ν C i) ⊆ ν C i (for some C) that is not an up-to
-- technique for C.

∃special-case-of-size-preserving×¬up-to :
  ∃ λ (I : Set) →
  ∃ λ (C : Container I I) →
  ∃ λ (F : Trans (# 0) I) →
      (∀ {i} → F (ν C i) ⊆ ν C i) × ¬ Up-to.Up-to-technique C F
∃special-case-of-size-preserving×¬up-to =
    (Proc × Proc)
  , S̲t̲e̲p̲
  , G
  , bisimilarity-pre-fixpoint
  , (Up-to-technique G                          ↝⟨ (λ up-to → up-to) ⟩
     (S ⊆ ⟦ S̲t̲e̲p̲ ⟧ (G S) → S ⊆ Bisimilarity ∞)  ↝⟨ (λ hyp below → hyp (Step↔S̲t̲e̲p̲ _ ∘ below)) ⟩
     (S ⊆ Step (G S) → S ⊆ Bisimilarity ∞)      ↝⟨ _$ S⊆StepGS ⟩
     S ⊆ Bisimilarity ∞                         ↝⟨ _$ pq ⟩
     Bisimilarity ∞ (p , q)                     ↝⟨ p≁q ⟩□
     ⊥                                          □)

  where

  data Proc : Set where
    p q r : Proc

  data _⟶_ : Proc → Proc → Set where
    p : p ⟶ p
    q : q ⟶ r

  lts = record
    { Proc      = Proc
    ; Label     = ⊤
    ; _[_]⟶_    = λ p _ q → p ⟶ q
    ; is-silent = λ _ → false
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

-- There is a relation transformer F satisfying
-- ∀ {i} → F (ν C i) ⊆ ν C i (for some C) that is not size-preserving
-- for C.

∃special-case-of-size-preserving×¬size-preserving :
  ∃ λ (I : Set) →
  ∃ λ (C : Container I I) →
  ∃ λ (F : Trans (# 0) I) →
      (∀ {i} → F (ν C i) ⊆ ν C i) × ¬ Up-to.Size-preserving C F
∃special-case-of-size-preserving×¬size-preserving =
  Σ-map id (Σ-map id (Σ-map id (Σ-map id
              (_∘ Up-to.size-preserving→up-to _))))
    ∃special-case-of-size-preserving×¬up-to

-- There is a monotone, extensive and size-preserving relation
-- transformer that is not compatible.

∃monotone×extensive×size-preserving×¬compatible :
  ∃ λ (lts : LTS lzero) →
  let open Combination lts in
  ∃ λ (F : Trans₂ (# 0) Proc) →
      Monotone F × Extensive F × Size-preserving F × ¬ Compatible F
∃monotone×extensive×size-preserving×¬compatible =
    one-transition
  , F
  , mono
  , extensive
  , pres
  , ¬comp

  where

  -- An LTS with two distinct processes and one transition from one to
  -- the other.

  one-transition : LTS lzero
  one-transition = record
    { Proc      = Bool
    ; Label     = ⊤
    ; _[_]⟶_    = λ x _ y → T (x ∧ not y)
    ; is-silent = λ _ → false
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

  -- F is size-preserving.

  pres : Size-preserving F
  pres = _⇔_.from (monotone→⇔ mono) (λ {_ x} → pre {x = x})

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

-- An LTS used in a couple of lemmas below, along with some
-- properties.

module PQR where

  -- An LTS with two sets of processes, three "to the left", and three
  -- "to the right".

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

  lts : LTS lzero
  lts = record
    { Proc      = Process
    ; Label     = Label
    ; _[_]⟶_    = _[_]⟶_
    ; is-silent = λ _ → false
    }

  open Combination lts public hiding (Label)

  -- Two relation transformers: F and G both add (at most) one pair to
  -- the underlying relation.

  data F (R : Rel₂ (# 0) Proc) : Rel₂ (# 0) Proc where
    qq  : F R (q left , q right)
    [_] : ∀ {x} → R x → F R x

  data G (R : Rel₂ (# 0) Proc) : Rel₂ (# 0) Proc where
    rr  : G R (r left , r right)
    [_] : ∀ {x} → R x → G R x

  -- A relation that adds one pair to reflexivity.

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

  -- The two processes q left and q right are not bisimilar.

  q≁q : ¬ q left ∼ q right
  q≁q =
    q left ∼ q right                                ↝⟨ (λ rel → S̲t̲e̲p̲.left-to-right rel qq) ⟩
    (∃ λ y → q right [ qq left ]⟶ y × q left ∼′ y)  ↝⟨ (λ { (_ , () , _) }) ⟩□
    ⊥                                               □

  -- The two processes r left and r right are not bisimilar.

  r≁r : ¬ r left ∼ r right
  r≁r =
    r left ∼ r right                                ↝⟨ (λ rel → S̲t̲e̲p̲.left-to-right rel rr) ⟩
    (∃ λ y → r right [ rr left ]⟶ y × r left ∼′ y)  ↝⟨ (λ { (_ , () , _) }) ⟩□
    ⊥                                               □

  -- F ∘ G is not an up-to technique.

  ¬-F∘G-up-to : ¬ Up-to-technique (F ∘ G)
  ¬-F∘G-up-to =
    Up-to-technique (F ∘ G)                    ↝⟨ (λ up-to → up-to R̲-prog′) ⟩
    R̲ ⊆ Bisimilarity ∞                         ↝⟨ (λ le → le pp) ⟩
    p left ∼ p right                           ↝⟨ (λ rel → S̲t̲e̲p̲.left-to-right rel pq) ⟩
    (∃ λ y → p right [ pq ]⟶ y × q left ∼′ y)  ↝⟨ (λ { (.(q right) , pq , rel) → rel }) ⟩
    q left ∼′ q right                          ↝⟨ (λ rel → q≁q (force rel)) ⟩
    ⊥                                          □

  module F-lemmas where

    -- F is monotone.

    mono : Monotone F
    mono R⊆S qq      = qq
    mono R⊆S [ Rxy ] = [ R⊆S Rxy ]

    -- F is extensive.

    ext : Extensive F
    ext = λ _ → [_]

    -- F is not size-preserving.

    ¬-pres : ¬ Size-preserving F
    ¬-pres =
      Size-preserving F                    ↝⟨ (λ pres → _⇔_.to (monotone→⇔ mono) pres) ⟩
      F (Bisimilarity ∞) ⊆ Bisimilarity ∞  ↝⟨ _$ qq ⟩
      q left ∼ q right                     ↝⟨ q≁q ⟩□
      ⊥                                    □

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

    -- G is not size-preserving.

    ¬-pres : ¬ Size-preserving G
    ¬-pres =
      Size-preserving G                    ↝⟨ (λ pres → _⇔_.to (monotone→⇔ mono) pres) ⟩
      G (Bisimilarity ∞) ⊆ Bisimilarity ∞  ↝⟨ _$ rr ⟩
      r left ∼ r right                     ↝⟨ r≁r ⟩□
      ⊥                                    □

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

-- There are monotone and extensive up-to techniques F and G such
-- that F ∘ G is not an up-to-technique.
--
-- Pous and Sangiorgi discuss another instance of this property in
-- Section 6.5.4 of "Enhancements of the bisimulation proof method".

∃[monotone×extensive×up-to]²×¬∘-up-to :
  ∃ λ (lts : LTS lzero) →
  let open Combination lts in
  ∃ λ (F : Trans₂ (# 0) Proc) →
  ∃ λ (G : Trans₂ (# 0) Proc) →
      Monotone F × Extensive F × Up-to-technique F ×
      Monotone G × Extensive G × Up-to-technique G ×
      ¬ Up-to-technique (F ∘ G)
∃[monotone×extensive×up-to]²×¬∘-up-to =
    lts
  , F
  , G
  , F-lemmas.mono
  , F-lemmas.ext
  , F-lemmas.up-to
  , G-lemmas.mono
  , G-lemmas.ext
  , G-lemmas.up-to
  , ¬-F∘G-up-to
  where
  open PQR

-- Up-to-technique is not closed under composition, not even for
-- monotone and extensive relation transformers.

¬-∘-closure :
  ∃ λ (lts : LTS lzero) →
  let open Combination lts in
  ¬ ({F G : Trans₂ (# 0) Proc} →
     Monotone F → Extensive F →
     Monotone G → Extensive G →
     Up-to-technique F →
     Up-to-technique G →
     Up-to-technique (F ∘ G))
¬-∘-closure =
    lts
  , λ ∘-closure →
        ¬-F∘G-up-to (∘-closure F-lemmas.mono F-lemmas.ext
                               G-lemmas.mono G-lemmas.ext
                               F-lemmas.up-to G-lemmas.up-to)
  where
  open PQR

-- There is a (monotone and extensive) up-to technique that is not
-- size-preserving.

∃monotone×extensive×up-to×¬size-preserving :
  ∃ λ (lts : LTS lzero) →
  let open Combination lts in
  ∃ λ (F : Trans₂ (# 0) Proc) →
      Monotone F × Extensive F × Up-to-technique F × ¬ Size-preserving F
∃monotone×extensive×up-to×¬size-preserving =
    lts
  , F
  , F-lemmas.mono
  , F-lemmas.ext
  , F-lemmas.up-to
  , F-lemmas.¬-pres
  where
  open PQR
