------------------------------------------------------------------------
-- Some counterexamples
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Bisimilarity.Up-to.Counterexamples where

open import Equality.Propositional
open import Logical-equivalence using (_⇔_)
open import Prelude

open import Bijection equality-with-J using (_↔_)
open import Fin equality-with-J
open import Function-universe equality-with-J hiding (id; _∘_)

open import Indexed-container using (⟦_⟧; force)
open import Labelled-transition-system

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
      using (Progression; progression; ⟪_,_⟫;
             Bisimulation; bisimulation⊆∼)
      renaming (_∼_ to _∼-cl_)
    open Bisimilarity.Coinductive lts public
    open Bisimilarity.Step lts (LTS._[_]⟶_ lts) public
      using (Step; Step↔S̲t̲e̲p̲)
    open Bisimilarity.Up-to lts public
    open LTS lts public hiding (_[_]⟶_)

-- Size-preserving relation transformers are not necessarily monotone.

¬size-preserving→monotone :
  ∃ λ lts → let open Combination lts in
  ¬ ((F : Trans₂ (# 0) Proc) → Size-preserving F → Monotone F)
¬size-preserving→monotone =
    one-loop
  , ((∀ G → Size-preserving G → Monotone G)  ↝⟨ (λ hyp → hyp _ F-pres) ⟩
     Monotone F                              ↝⟨ ¬-F-mono ⟩□
     ⊥                                       □)
  where
  open Combination one-loop

  F : Trans₂ (# 0) Proc
  F R = ¬_ ∘ R

  ¬-F-mono : ¬ Monotone F
  ¬-F-mono =
    Monotone F                                                   ↝⟨ (λ mono → mono {_}) ⟩
    ((λ _ → ⊥) ⊆ (λ _ → ↑ _ ⊤) → F (λ _ → ⊥) ⊆ F (λ _ → ↑ _ ⊤))  ↔⟨⟩
    ((λ _ → ⊥) ⊆ (λ _ → ↑ _ ⊤) → (λ _ → ¬ ⊥) ⊆ (λ _ → ¬ ↑ _ ⊤))  ↝⟨ _$ _ ⟩
    (λ _ → ¬ ⊥) ⊆ (λ _ → ¬ ↑ _ ⊤)                                ↝⟨ (_$ _) ⟩
    (¬ ⊥ → ¬ ↑ _ ⊤)                                              ↝⟨ _$ ⊥-elim ⟩
    ¬ ↑ _ ⊤                                                      ↝⟨ _$ _ ⟩□
    ⊥                                                            □

  total : ∀ {i x y} → [ i ] x ∼ y
  total = reflexive

  F-pres : Size-preserving F
  F-pres _ _ _ = total

-- Monotone, size-preserving relation transformers are not necessarily
-- compatible.

¬monotone→size-preserving→compatible :
  ∃ λ lts → let open Combination lts in
  ¬ ((F : Trans₂ (# 0) Proc) →
     Monotone F → Size-preserving F → Compatible F)
¬monotone→size-preserving→compatible =
    one-transition

  , ((∀ F → Monotone F → Size-preserving F → Compatible F)  ↝⟨ (λ hyp → hyp F mono (_⇔_.from (monotone→⇔ mono) pre)) ⟩
     Compatible F                                           ↝⟨ ¬comp ⟩□
     ⊥                                                      □)

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
  F R (true , true) = R (false , false)
  F R               = R

  -- F is monotone.

  mono : Monotone F
  mono R⊆S (true  , true)  = R⊆S _
  mono R⊆S (true  , false) = R⊆S _
  mono R⊆S (false , true)  = R⊆S _
  mono R⊆S (false , false) = R⊆S _

  -- Bisimilarity of size i is a pre-fixpoint of F.

  pre : ∀ {i} → F (Bisimilarity i) ⊆ Bisimilarity i
  pre (true  , true)  = λ _ → true ■
  pre (true  , false) = id
  pre (false , true)  = id
  pre (false , false) = id

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
    Compatible F                                                   ↝⟨ (λ comp → comp) ⟩
    F (⟦ S̲t̲e̲p̲ ⟧ R) ⊆ ⟦ S̲t̲e̲p̲ ⟧ (F R)                                ↝⟨ (λ le → le (true , true)) ⟩
    (F (⟦ S̲t̲e̲p̲ ⟧ R) (true , true) → ⟦ S̲t̲e̲p̲ ⟧ (F R) (true , true))  ↔⟨⟩
    (⟦ S̲t̲e̲p̲ ⟧ R (false , false) → ⟦ S̲t̲e̲p̲ ⟧ (F R) (true , true))    ↝⟨ _$ _↔_.to Step↔S̲t̲e̲p̲ StepRff ⟩
    ⟦ S̲t̲e̲p̲ ⟧ (F R) (true , true)                                   ↝⟨ (λ step → S̲t̲e̲p̲.left-to-right {p = true} {q = true} step {p′ = false} _ ) ⟩
    (∃ λ y → T (not y) × F R (false , y))                          ↔⟨⟩
    (∃ λ y → T (not y) × R (false , y))                            ↝⟨ uncurry [ const proj₁ , const (⊥-elim ∘ proj₂) ] ⟩□
    ⊥                                                              □

-- Up-to-technique is not closed under composition, not even for
-- monotone relation transformers.
--
-- (Pous and Sangiorgi mention two other counterexamples to this
-- property in "Enhancements of the bisimulation proof method".)

¬-∘-closure :
  ∃ λ lts → let open Combination lts in
  ¬ ({F G : Trans₂ (# 0) Proc} →
     Monotone F →
     Monotone G →
     Up-to-technique F →
     Up-to-technique G →
     Up-to-technique (F ∘ G))
¬-∘-closure =
    lts

  , ((∀ {F G} → Monotone F → Monotone G →
      Up-to-technique F → Up-to-technique G → Up-to-technique (F ∘ G))  ↝⟨ (λ cl → cl F-lemmas.mono G-lemmas.mono F-lemmas.up-to G-lemmas.up-to) ⟩

     Up-to-technique (F ∘ G)                                            ↝⟨ (λ up-to → up-to R̲-prog′) ⟩

     R̲ ⊆ Bisimilarity ∞                                                 ↝⟨ (λ le → le _ pp) ⟩

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
  R̲-prog =
    ⟪ flip (λ where
              pq pp   → _ , pq , qq
              pq refl → _ , pq , [ [ refl ] ]
              pr pp   → _ , pr , [ rr       ]
              pr refl → _ , pr , [ [ refl ] ]
              qq refl → _ , qq , [ [ refl ] ]
              rr refl → _ , rr , [ [ refl ] ])
    , flip (λ where
              pq pp   → _ , pq , qq
              pq refl → _ , pq , [ [ refl ] ]
              pr pp   → _ , pr , [ rr       ]
              pr refl → _ , pr , [ [ refl ] ]
              qq refl → _ , qq , [ [ refl ] ]
              rr refl → _ , rr , [ [ refl ] ])
    ⟫

  R̲-prog′ : R̲ ⊆ ⟦ S̲t̲e̲p̲ ⟧ (F (G R̲))
  R̲-prog′ = (_↔_.to Step↔S̲t̲e̲p̲ ∘_) ∘ progression R̲-prog

  module F-lemmas where

    -- F is monotone.

    mono : Monotone F
    mono R⊆S _ qq      = qq
    mono R⊆S _ [ Rxy ] = [ R⊆S _ Rxy ]

    -- F is an up-to technique.

    module _ {R} (R-prog′ : R ⊆ ⟦ S̲t̲e̲p̲ ⟧ (F R)) where

      R-prog : Progression R (F R)
      progression R-prog = (_↔_.from Step↔S̲t̲e̲p̲ ∘_) ∘ R-prog′

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
      up-to (p left  , p left)  rel = reflexive
      up-to (p left  , p right) rel = ⊥-elim (¬pp rel)
      up-to (p right , p left)  rel = ⊥-elim (¬pp rel)
      up-to (p right , p right) rel = reflexive
      up-to (p _     , q _)     rel = ⊥-elim (¬pq rel)
      up-to (p _     , r _)     rel = ⊥-elim (¬pr rel)
      up-to (q _     , p _)     rel = ⊥-elim (¬qp rel)
      up-to (q left  , q left)  rel = reflexive
      up-to (q left  , q right) rel = ⊥-elim (¬qq rel)
      up-to (q right , q left)  rel = ⊥-elim (¬qq rel)
      up-to (q right , q right) rel = reflexive
      up-to (q _     , r _)     rel = ⊥-elim (¬qr rel)
      up-to (r _     , p _)     rel = ⊥-elim (¬rp rel)
      up-to (r _     , q _)     rel = ⊥-elim (¬rq rel)
      up-to (r left  , r left)  rel = reflexive
      up-to (r left  , r right) rel = ⊥-elim (¬rr rel)
      up-to (r right , r left)  rel = ⊥-elim (¬rr rel)
      up-to (r right , r right) rel = reflexive

  module G-lemmas where

    -- G is monotone.

    mono : Monotone G
    mono R⊆S _ rr      = rr
    mono R⊆S _ [ Rxy ] = [ R⊆S _ Rxy ]

    -- G is an up-to technique.

    module _ {R} (R-prog′ : R ⊆ ⟦ S̲t̲e̲p̲ ⟧ (G R)) where

      R-prog : Progression R (G R)
      progression R-prog = (_↔_.from Step↔S̲t̲e̲p̲ ∘_) ∘ R-prog′

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
      up-to (p left  , p left)  rel = reflexive
      up-to (p left  , p right) rel = ⊥-elim (¬pp rel)
      up-to (p right , p left)  rel = ⊥-elim (¬pp rel)
      up-to (p right , p right) rel = reflexive
      up-to (p _     , q _)     rel = ⊥-elim (¬pq rel)
      up-to (p _     , r _)     rel = ⊥-elim (¬pr rel)
      up-to (q _     , p _)     rel = ⊥-elim (¬qp rel)
      up-to (q left  , q left)  rel = reflexive
      up-to (q left  , q right) rel = ⊥-elim (¬qq rel)
      up-to (q right , q left)  rel = ⊥-elim (¬qq rel)
      up-to (q right , q right) rel = reflexive
      up-to (q _     , r _)     rel = ⊥-elim (¬qr rel)
      up-to (r _     , p _)     rel = ⊥-elim (¬rp rel)
      up-to (r _     , q _)     rel = ⊥-elim (¬rq rel)
      up-to (r left  , r left)  rel = reflexive
      up-to (r left  , r right) rel = ⊥-elim (¬rr rel)
      up-to (r right , r left)  rel = ⊥-elim (¬rr rel)
      up-to (r right , r right) rel = reflexive

-- Up-to techniques are not necessarily size-preserving, not even if
-- they are monotone.

¬monotone→up-to→size-preserving :
  ∃ λ lts → let open Combination lts in
  ¬ ((F : Trans₂ (# 0) Proc) →
     Monotone F → Up-to-technique F → Size-preserving F)
¬monotone→up-to→size-preserving =
  let lts , ¬-∘-closure = ¬-∘-closure
      open Combination lts
  in

    lts

  , λ monotone→up-to→size-preserving →

    ¬-∘-closure λ {F G} F-mono G-mono F-up-to G-up-to →  $⟨ ((λ {_ _} → F-mono) , (λ {_} → F-up-to)) , ((λ {_ _} → G-mono) , (λ {_} → G-up-to)) ⟩

      (Monotone F × Up-to-technique F) ×
      (Monotone G × Up-to-technique G)                   ↝⟨ Σ-map (uncurry $ monotone→up-to→size-preserving _)
                                                                  (uncurry $ monotone→up-to→size-preserving _) ⟩

      Size-preserving F × Size-preserving G              ↝⟨ uncurry ∘-closure ⟩

      Size-preserving (F ∘ G)                            ↝⟨ size-preserving→up-to ⟩□

      Up-to-technique (F ∘ G)                            □
