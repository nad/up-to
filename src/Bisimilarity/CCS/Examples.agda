------------------------------------------------------------------------
-- Some results/examples related to CCS, implemented using the
-- coinductive definition of bisimilarity
------------------------------------------------------------------------

-- Unless anything else is stated the results (or statements, in the
-- case of exercises) below are taken from "Enhancements of the
-- bisimulation proof method" by Pous and Sangiorgi.

{-# OPTIONS --without-K --safe --sized-types #-}

module Bisimilarity.CCS.Examples {ℓ} {Name : Set ℓ} where

open import Equality.Propositional
open import Prelude

open import Bisimilarity.CCS
import Bisimilarity.Equational-reasoning-instances
open import Equational-reasoning
open import Labelled-transition-system.CCS Name

open import Bisimilarity CCS

------------------------------------------------------------------------
-- A result mentioned in "Enhancements of the bisimulation proof
-- method"

mutual

  -- For a more general result, see 6-2-14 below.

  !∙⊕∙∼!∙∣!∙ : ∀ {i a b} → [ i ] ! (a ∙ ⊕ b ∙) ∼ ! a ∙ ∣ ! b ∙
  !∙⊕∙∼!∙∣!∙ {i} {a} {b} = ⟨ lr , rl ⟩
    where
    lemma =
      ! (a ∙ ⊕ b ∙) ∣ ∅  ∼⟨ ∣-right-identity ⟩
      ! (a ∙ ⊕ b ∙)      ∼⟨ !∙⊕∙∼′!∙∣!∙ {i = i} ⟩■
      ! a ∙ ∣ ! b ∙

    left-lemma =
      ! (a ∙ ⊕ b ∙) ∣ ∅    ∼⟨ lemma ⟩
      ! a ∙ ∣ ! b ∙        ∼⟨ symmetric ∣-right-identity ∣-cong reflexive ⟩■
      (! a ∙ ∣ ∅) ∣ ! b ∙

    right-lemma =
      ! (a ∙ ⊕ b ∙) ∣ ∅    ∼⟨ lemma ⟩
      ! a ∙ ∣  ! b ∙       ∼⟨ reflexive ∣-cong symmetric ∣-right-identity ⟩■
      ! a ∙ ∣ (! b ∙ ∣ ∅)

    τ-lemma =
      (! (a ∙ ⊕ b ∙) ∣ ∅) ∣ ∅    ∼⟨ ∣-right-identity ⟩
      ! (a ∙ ⊕ b ∙) ∣ ∅          ∼⟨ lemma ⟩
      ! a ∙ ∣ ! b ∙              ∼⟨ symmetric (∣-right-identity ∣-cong ∣-right-identity) ⟩■
      (! a ∙ ∣ ∅) ∣ (! b ∙ ∣ ∅)

    lr : ∀ {P μ} →
         ! (a ∙ ⊕ b ∙) [ μ ]⟶ P →
         ∃ λ Q → ! a ∙ ∣ ! b ∙ [ μ ]⟶ Q × [ i ] P ∼′ Q
    lr {P} tr = case 6-1-3-2 tr of λ where

      (inj₁ (.∅ , sum-left action , P∼![a⊕b]∣∅)) →
        P                    ∼⟨ P∼![a⊕b]∣∅ ⟩
        ! (a ∙ ⊕ b ∙) ∣ ∅    ∼⟨ left-lemma ⟩■
        (! a ∙ ∣ ∅) ∣ ! b ∙  [ name a ]⟵⟨ par-left (replication (par-right action)) ⟩
        ! a ∙       ∣ ! b ∙

      (inj₁ (.∅ , sum-right action , P∼![a⊕b]∣∅)) →
        P                    ∼⟨ P∼![a⊕b]∣∅ ⟩
        ! (a ∙ ⊕ b ∙) ∣ ∅    ∼⟨ right-lemma ⟩■
        ! a ∙ ∣ (! b ∙ ∣ ∅)  [ name b ]⟵⟨ par-right (replication (par-right action)) ⟩
        ! a ∙ ∣ ! b ∙

      (inj₂ (refl , P′ , P″ , c , a⊕b⟶P′ , a⊕b⟶P″ , P∼![a⊕b]∣P′∣P″)) →
        let b≡co-a , P′≡∅ , P″≡∅ = Σ-map id [ id , id ]
                                     (·⊕·-co a⊕b⟶P′ a⊕b⟶P″) in

        P                          ∼⟨ P∼![a⊕b]∣P′∣P″ ⟩
        (! (a ∙ ⊕ b ∙) ∣ P′) ∣ P″  ∼⟨ (reflexive ∣-cong ≡⇒∼ P′≡∅) ∣-cong ≡⇒∼ P″≡∅ ⟩
        (! (a ∙ ⊕ b ∙) ∣ ∅) ∣ ∅    ∼⟨ τ-lemma ⟩■
        (! a ∙ ∣ ∅) ∣ (! b ∙ ∣ ∅)  [ τ ]⟵⟨ par-τ′ b≡co-a (replication (par-right action))
                                                         (replication (par-right action)) ⟩
        ! a ∙ ∣ ! b ∙

    rl : ∀ {Q μ} →
         ! a ∙ ∣ ! b ∙ [ μ ]⟶ Q →
         ∃ λ P → ! (a ∙ ⊕ b ∙) [ μ ]⟶ P × [ i ] P ∼′ Q
    rl (par-left {P′ = P′} tr) =
      case 6-1-3-2 tr of λ where

        (inj₁ (.∅ , action , P′∼!a∣∅)) →
          ! (a ∙ ⊕ b ∙)        [ name a ]⟶⟨ replication (par-right (sum-left action)) ⟩ʳˡ
          ! (a ∙ ⊕ b ∙) ∣ ∅    ∼⟨ left-lemma ⟩
          (! a ∙ ∣ ∅) ∣ ! b ∙  ∼⟨ symmetric P′∼!a∣∅ ∣-cong reflexive ⟩■
          P′ ∣ ! b ∙

        (inj₂ (refl , .∅ , P″ , .a , action , a⟶P″ , P′∼!a∣∅∣P″)) →
          ⊥-elim (names-are-not-inverted a⟶P″)

    rl (par-right {Q′ = Q′} tr) =
      case 6-1-3-2 tr of λ where

        (inj₁ (.∅ , action , Q′∼!b∣∅)) →
          ! (a ∙ ⊕ b ∙)        [ name b ]⟶⟨ replication (par-right (sum-right action)) ⟩ʳˡ
          ! (a ∙ ⊕ b ∙) ∣ ∅    ∼⟨ right-lemma ⟩
          ! a ∙ ∣ (! b ∙ ∣ ∅)  ∼⟨ reflexive ∣-cong symmetric Q′∼!b∣∅ ⟩■
          ! a ∙ ∣ Q′

        (inj₂ (refl , .∅ , Q″ , .b , action , b⟶Q″ , Q′∼!b∣∅∣Q″)) →
          ⊥-elim (names-are-not-inverted b⟶Q″)

    rl (par-τ {P′ = P′} {Q′ = Q′} tr₁ tr₂) =
      case 6-1-3-2 tr₁ ,′ 6-1-3-2 tr₂ of λ where

        (inj₁ (.∅ , action , P′∼!a∣∅) ,
         inj₁ (.∅ , action , Q′∼!co-a∣∅)) →
          ! (a ∙ ⊕ co a ∙)              [ τ ]⟶⟨ replication (par-τ (replication (par-right (sum-left action)))
                                                                   (sum-right action)) ⟩ʳˡ
          (! (a ∙ ⊕ co a ∙) ∣ ∅) ∣ ∅    ∼⟨ τ-lemma ⟩
          (! a ∙ ∣ ∅) ∣ (! co a ∙ ∣ ∅)  ∼⟨ symmetric (P′∼!a∣∅ ∣-cong Q′∼!co-a∣∅) ⟩■
          P′ ∣ Q′

        (inj₁ _ , inj₂ (() , _))
        (inj₂ (() , _) , _)

  !∙⊕∙∼′!∙∣!∙ : ∀ {a b i} → [ i ] ! (a ∙ ⊕ b ∙) ∼′ ! a ∙ ∣ ! b ∙
  force !∙⊕∙∼′!∙∣!∙ = !∙⊕∙∼!∙∣!∙

------------------------------------------------------------------------
-- Exercise 6.2.4

mutual

  -- For a more general result, see 6-2-17-4 below.

  6-2-4 : ∀ {a i} → [ i ] ! ! a ∙ ∼ ! a ∙
  6-2-4 {a} {i} = ⟨ lr , rl ⟩
    where
    impossible : ∀ {μ P q} {Q : Set q} →
                 ! ! a ∙ [ μ ]⟶ P → μ ≡ τ → Q
    impossible {μ} !!a⟶P μ≡τ = ⊥-elim $ name≢τ
      (name a  ≡⟨ !-only (!-only ·-only) !!a⟶P ⟩
       μ       ≡⟨ μ≡τ ⟩∎
       τ       ∎)

    lemma = λ {P : Proc ∞} P∼!a∣∅ →
      ! ! a ∙ ∣ P            ∼⟨ reflexive ∣-cong P∼!a∣∅ ⟩
      ! ! a ∙ ∣ (! a ∙ ∣ ∅)  ∼⟨ reflexive ∣-cong ∣-right-identity ⟩
      ! ! a ∙ ∣ ! a ∙        ∼⟨ 6-1-2 ⟩
      ! ! a ∙                ∼⟨ 6-2-4′ {i = i} ⟩
      ! a ∙                  ∼⟨ symmetric ∣-right-identity ⟩■
      ! a ∙ ∣ ∅

    lr : ∀ {P μ} →
         ! ! a ∙ [ μ ]⟶ P →
         ∃ λ P′ → ! a ∙ [ μ ]⟶ P′ × [ i ] P ∼′ P′
    lr {P = P} !!a⟶P = case 6-1-3-2 !!a⟶P of λ where
      (inj₂ (μ≡τ , _))               → impossible !!a⟶P μ≡τ
      (inj₁ (P′ , !a⟶P′ , P∼!!a∣P′)) → case 6-1-3-2 !a⟶P′ of λ where
        (inj₂ (μ≡τ , _))               → impossible !!a⟶P μ≡τ
        (inj₁ (.∅ , action , P′∼!a∣∅)) →
          P             ∼⟨ P∼!!a∣P′ ⟩
          ! ! a ∙ ∣ P′  ∼⟨ lemma P′∼!a∣∅ ⟩■
          ! a ∙ ∣ ∅     [ name a ]⟵⟨ replication (par-right action) ⟩
          ! a ∙

    rl : ∀ {P μ} →
         ! a ∙ [ μ ]⟶ P →
         ∃ λ P′ → ! ! a ∙ [ μ ]⟶ P′ × [ i ] P′ ∼′ P
    rl {P = P} !a⟶P = case 6-1-3-2 !a⟶P of λ where
      (inj₂ (refl , .∅ , Q″ , .a , action , a⟶Q″ , _)) →
        ⊥-elim (names-are-not-inverted a⟶Q″)
      (inj₁ (.∅ , action , P∼!a∣∅)) →
        ! ! a ∙      [ name a ]⟶⟨ replication (par-right !a⟶P) ⟩ʳˡ
        ! ! a ∙ ∣ P  ∼⟨ lemma P∼!a∣∅ ⟩
        ! a ∙ ∣ ∅    ∼⟨ symmetric P∼!a∣∅ ⟩■
        P

  6-2-4′ : ∀ {a i} → [ i ] ! ! a ∙ ∼′ ! a ∙
  force 6-2-4′ = 6-2-4

------------------------------------------------------------------------
-- A result mentioned in "Enhancements of the bisimulation proof
-- method"

∙∣∙∼∙∙ : ∀ {a} → a ∙ ∣ a ∙ ∼ name a ∙ (a ∙)
∙∣∙∼∙∙ {a} = ⟨ lr , rl ⟩
  where
  lr : ∀ {P μ} → a ∙ ∣ a ∙ [ μ ]⟶ P →
       ∃ λ P′ → name a ∙ (a ∙) [ μ ]⟶ P′ × P ∼′ P′
  lr (par-left action) =
    ∅ ∣ a ∙         ∼⟨ ∣-left-identity ⟩■
    a ∙             [ name a ]⟵⟨ action ⟩
    name a ∙ (a ∙)

  lr (par-right action) =
    a ∙ ∣ ∅         ∼⟨ ∣-right-identity ⟩■
    a ∙             [ name a ]⟵⟨ action ⟩
    name a ∙ (a ∙)

  lr (par-τ action tr) = ⊥-elim (names-are-not-inverted tr)

  rl : ∀ {P μ} → name a ∙ (a ∙) [ μ ]⟶ P →
       ∃ λ P′ → a ∙ ∣ a ∙ [ μ ]⟶ P′ × P′ ∼′ P
  rl action =
    a ∙ ∣ a ∙  [ name a ]⟶⟨ par-right action ⟩ʳˡ
    a ∙ ∣ ∅    ∼⟨ ∣-right-identity ⟩■
    a ∙

------------------------------------------------------------------------
-- Lemma 6.2.14

mutual

  -- A more general variant of !∙⊕∙∼!∙∣!∙. For an even more general
  -- variant, see 6-2-17-2 below.

  6-2-14 :
    ∀ {i a b P Q} →
    [ i ] ! (name a ∙ P ⊕ name b ∙ Q) ∼ ! name a ∙ P ∣ ! name b ∙ Q
  6-2-14 {i} {a} {b} {P} {Q} = ⟨ lr , rl ⟩
    where
    left-lemma =
      ! (name a ∙ P ⊕ name b ∙ Q) ∣ P    ∼⟨ 6-2-14′ {i = i} ∣-cong′ reflexive ⟩
      (! name a ∙ P ∣ ! name b ∙ Q) ∣ P  ∼⟨ swap-rightmost ⟩■
      (! name a ∙ P ∣ P) ∣ ! name b ∙ Q

    right-lemma =
      ! (name a ∙ P ⊕ name b ∙ Q) ∣ Q    ∼⟨ 6-2-14′ {i = i} ∣-cong′ reflexive ⟩
      (! name a ∙ P ∣ ! name b ∙ Q) ∣ Q  ∼⟨ symmetric ∣-assoc ⟩■
      ! name a ∙ P ∣ (! name b ∙ Q ∣ Q)

    τ-lemma =
      (! (name a ∙ P ⊕ name b ∙ Q) ∣ P) ∣ Q    ∼⟨ left-lemma ∣-cong′ reflexive ⟩
      ((! name a ∙ P ∣ P) ∣ ! name b ∙ Q) ∣ Q  ∼⟨ symmetric ∣-assoc ⟩■
      (! name a ∙ P ∣ P) ∣ (! name b ∙ Q ∣ Q)

    lr : ∀ {R μ} →
         ! (name a ∙ P ⊕ name b ∙ Q) [ μ ]⟶ R →
         ∃ λ S → ! name a ∙ P ∣ ! name b ∙ Q [ μ ]⟶ S × [ i ] R ∼′ S
    lr {R} tr = case 6-1-3-2 tr of λ where

      (inj₁ (.P , sum-left action , R∼![aP⊕bQ]∣P)) →
        R                                  ∼⟨ R∼![aP⊕bQ]∣P ⟩
        ! (name a ∙ P ⊕ name b ∙ Q) ∣ P    ∼⟨ left-lemma ⟩■
        (! name a ∙ P ∣ P) ∣ ! name b ∙ Q  [ name a ]⟵⟨ par-left (replication (par-right action)) ⟩
        ! name a ∙ P       ∣ ! name b ∙ Q

      (inj₁ (.Q , sum-right action , R∼![aP⊕bQ]∣Q)) →
        R                                  ∼⟨ R∼![aP⊕bQ]∣Q ⟩
        ! (name a ∙ P ⊕ name b ∙ Q) ∣ Q    ∼⟨ right-lemma ⟩■
        ! name a ∙ P ∣ (! name b ∙ Q ∣ Q)  [ name b ]⟵⟨ par-right (replication (par-right action)) ⟩
        ! name a ∙ P ∣ ! name b ∙ Q

      (inj₂ ( refl , R′ , R″ , c , aP⊕bQ⟶R′ , aP⊕bQ⟶R″
            , R∼![aP⊕bQ]∣R′∣R″
            )) →
        let b≡co-a , R′≡,R″≡ = ·⊕·-co aP⊕bQ⟶R′ aP⊕bQ⟶R″

            lemma : _ → [ _ ] _ ∼ _
            lemma = λ where
              (inj₁ (R′≡P , R″≡Q)) →
                (! (name a ∙ P ⊕ name b ∙ Q) ∣ R′) ∣ R″  ∼⟨ (reflexive ∣-cong ≡⇒∼ R′≡P) ∣-cong ≡⇒∼ R″≡Q ⟩■
                (! (name a ∙ P ⊕ name b ∙ Q) ∣ P) ∣ Q
              (inj₂ (R′≡Q , R″≡P)) →
                (! (name a ∙ P ⊕ name b ∙ Q) ∣ R′) ∣ R″  ∼⟨ (reflexive ∣-cong ≡⇒∼ R′≡Q) ∣-cong ≡⇒∼ R″≡P ⟩
                (! (name a ∙ P ⊕ name b ∙ Q) ∣ Q) ∣ P    ∼⟨ swap-rightmost ⟩■
                (! (name a ∙ P ⊕ name b ∙ Q) ∣ P) ∣ Q
        in
        R                                        ∼⟨ R∼![aP⊕bQ]∣R′∣R″ ⟩
        (! (name a ∙ P ⊕ name b ∙ Q) ∣ R′) ∣ R″  ∼⟨ lemma R′≡,R″≡ ⟩
        (! (name a ∙ P ⊕ name b ∙ Q) ∣ P) ∣ Q    ∼⟨ τ-lemma ⟩■
        (! name a ∙ P ∣ P) ∣ (! name b ∙ Q ∣ Q)  [ τ ]⟵⟨ par-τ′ b≡co-a (replication (par-right action))
                                                                       (replication (par-right action)) ⟩
        ! name a ∙ P ∣ ! name b ∙ Q

    rl : ∀ {S μ} →
         ! name a ∙ P ∣ ! name b ∙ Q [ μ ]⟶ S →
         ∃ λ R → ! (name a ∙ P ⊕ name b ∙ Q) [ μ ]⟶ R × [ i ] R ∼′ S
    rl (par-left {P′ = S} tr) =
      case 6-1-3-2 tr of λ where
        (inj₁ (.P , action , S∼!aP∣P)) →
          ! (name a ∙ P ⊕ name b ∙ Q)        [ name a ]⟶⟨ replication (par-right (sum-left action)) ⟩ʳˡ
          ! (name a ∙ P ⊕ name b ∙ Q) ∣ P    ∼⟨ left-lemma ⟩
          (! name a ∙ P ∣ P) ∣ ! name b ∙ Q  ∼⟨ symmetric S∼!aP∣P ∣-cong reflexive ⟩■
          S ∣ ! name b ∙ Q

        (inj₂ (refl , .P , S′ , .a , action , aP⟶S′ , S∼!aP∣P∣S′)) →
          ⊥-elim (names-are-not-inverted aP⟶S′)

    rl (par-right {Q′ = S} tr) =
      case 6-1-3-2 tr of λ where
        (inj₁ (.Q , action , S∼!bQ∣Q)) →
          ! (name a ∙ P ⊕ name b ∙ Q)        [ name b ]⟶⟨ replication (par-right (sum-right action)) ⟩ʳˡ
          ! (name a ∙ P ⊕ name b ∙ Q) ∣ Q    ∼⟨ right-lemma ⟩
          ! name a ∙ P ∣ (! name b ∙ Q ∣ Q)  ∼⟨ reflexive ∣-cong symmetric S∼!bQ∣Q ⟩■
          ! name a ∙ P ∣ S

        (inj₂ (refl , .Q , S′ , .b , action , bQ⟶S′ , S∼!bQ∣Q∣S′)) →
          ⊥-elim (names-are-not-inverted bQ⟶S′)

    rl (par-τ {P′ = S} {Q′ = S′} tr₁ tr₂) =
      case 6-1-3-2 tr₁ ,′ 6-1-3-2 tr₂ of λ where
        (inj₁ (.P , action , S∼!aP∣P) ,
         inj₁ (.Q , action , S′∼!co-aQ∣Q)) →
          ! (name a ∙ P ⊕ name (co a) ∙ Q)              [ τ ]⟶⟨ replication (par-τ (replication (par-right (sum-left action)))
                                                                                   (sum-right action)) ⟩ʳˡ
          (! (name a ∙ P ⊕ name (co a) ∙ Q) ∣ P) ∣ Q    ∼⟨ τ-lemma ⟩
          (! name a ∙ P ∣ P) ∣ (! name (co a) ∙ Q ∣ Q)  ∼⟨ symmetric (S∼!aP∣P ∣-cong S′∼!co-aQ∣Q) ⟩■
          S ∣ S′

        (inj₁ _ , inj₂ (() , _))
        (inj₂ (() , _) , _)

  6-2-14′ :
    ∀ {i a b P Q} →
    [ i ] ! (name a ∙ P ⊕ name b ∙ Q) ∼′ ! name a ∙ P ∣ ! name b ∙ Q
  force 6-2-14′ = 6-2-14

------------------------------------------------------------------------
-- Lemma 6.2.17

-- Some results mentioned in the proof of 6.2.17 (1) in
-- "Enhancements of the bisimulation proof method".

6-2-17-1-lemma₁ : ∀ {P Q} → (! P ∣ ! Q) ∣ (P ∣ Q) ∼ ! P ∣ ! Q
6-2-17-1-lemma₁ {P} {Q} =
  (! P ∣ ! Q) ∣ (P ∣ Q)  ∼⟨ swap-in-the-middle ⟩
  (! P ∣ P) ∣ (! Q ∣ Q)  ∼⟨ 6-1-2 ∣-cong 6-1-2 ⟩■
  ! P ∣ ! Q

abstract

  6-2-17-1-lemma₂ :
    ∀ {P Q R μ} →
    ! (P ∣ Q) [ μ ]⟶ R →
    ∃ λ S →
      R ∼ ! (P ∣ Q) ∣ S ×
      ∃ λ T →
        ! P ∣ ! Q [ μ ]⟶ T ×
        (! P ∣ ! Q) ∣ S ∼′ T
  6-2-17-1-lemma₂ {P} {Q} {R} tr = case 6-1-3-2 tr of λ where
    (inj₁ (R′ , P∣Q⟶R′ , R∼![P∣Q]∣R′)) →
      let R″ , !P∣!Q⟶R″ , !P∣!Q∣R′∼R″ =
            left-to-right
              ((! P ∣ ! Q) ∣ (P ∣ Q)  ∼⟨ 6-2-17-1-lemma₁ ⟩■
               ! P ∣ ! Q)
              ((! P ∣ ! Q) ∣ (P ∣ Q)  ⟶⟨ par-right P∣Q⟶R′ ⟩
               (! P ∣ ! Q) ∣ R′)
      in _ , R∼![P∣Q]∣R′ , _ , !P∣!Q⟶R″ , !P∣!Q∣R′∼R″

    (inj₂ (refl , R′ , R″ , a , P∣Q⟶R′ , P∣Q⟶R″ , R∼![P∣Q]∣R′∣R″)) →
      let T , !P∣!Q⟶T , !P∣!Q∣[R′∣R″]∼T =
            left-to-right
              ((! P ∣ ! Q) ∣ ((P ∣ Q) ∣ (P ∣ Q))  ∼⟨ ∣-assoc ⟩
               ((! P ∣ ! Q) ∣ (P ∣ Q)) ∣ (P ∣ Q)  ∼⟨ 6-2-17-1-lemma₁ ∣-cong reflexive ⟩
               (! P ∣ ! Q) ∣ (P ∣ Q)              ∼⟨ 6-2-17-1-lemma₁ ⟩■
               ! P ∣ ! Q)
              ((! P ∣ ! Q) ∣ ((P ∣ Q) ∣ (P ∣ Q))  ⟶⟨ par-right (par-τ P∣Q⟶R′ P∣Q⟶R″) ⟩
               (! P ∣ ! Q) ∣ (R′ ∣ R″))
      in
        _
      , (R                      ∼⟨ R∼![P∣Q]∣R′∣R″ ⟩
         (! (P ∣ Q) ∣ R′) ∣ R″  ∼⟨ symmetric ∣-assoc ⟩■
         ! (P ∣ Q) ∣ (R′ ∣ R″))
      , _
      , !P∣!Q⟶T
      , !P∣!Q∣[R′∣R″]∼T

mutual

  6-2-17-1 : ∀ {i P Q} → [ i ] ! (P ∣ Q) ∼ ! P ∣ ! Q
  6-2-17-1 {i} {P} {Q} = ⟨ lr , rl ⟩
    where
    lr : ∀ {R μ} →
         ! (P ∣ Q) [ μ ]⟶ R →
         ∃ λ S → ! P ∣ ! Q [ μ ]⟶ S × [ i ] R ∼′ S
    lr {R} tr =
      let S , R∼![P∣Q]∣S , T , !P∣!Q⟶T , !P∣!Q∣S∼T =
            6-2-17-1-lemma₂ tr in

      R                ∼⟨ R∼![P∣Q]∣S ⟩
      ! (P ∣ Q) ∣ S    ∼⟨ 6-2-17-1′ ∣-cong′ reflexive ⟩
      (! P ∣ ! Q) ∣ S  ∼⟨ !P∣!Q∣S∼T ⟩■
      T                ⟵⟨ !P∣!Q⟶T ⟩
      ! P ∣ ! Q

    lemma = λ {R S : Proc ∞} →
      ! (P ∣ Q) ∣ (R ∣ S)    ∼⟨ 6-2-17-1′ {i = i} ∣-cong′ reflexive ⟩
      (! P ∣ ! Q) ∣ (R ∣ S)  ∼⟨ swap-in-the-middle ⟩■
      (! P ∣ R) ∣ (! Q ∣ S)

    left-lemma = λ {R : Proc ∞} →
      ! (P ∣ Q) ∣ (R ∣ Q)    ∼⟨ lemma ⟩
      (! P ∣ R) ∣ (! Q ∣ Q)  ∼⟨ reflexive ∣-cong 6-1-2 ⟩■
      (! P ∣ R) ∣ ! Q

    right-lemma = λ {R : Proc ∞} →
      ! (P ∣ Q) ∣ (P ∣ R)    ∼⟨ lemma ⟩
      (! P ∣ P) ∣ (! Q ∣ R)  ∼⟨ 6-1-2 ∣-cong reflexive ⟩■
      ! P ∣ (! Q ∣ R)

    rl : ∀ {S μ} →
         ! P ∣ ! Q [ μ ]⟶ S →
         ∃ λ R → ! (P ∣ Q) [ μ ]⟶ R × [ i ] R ∼′ S
    rl (par-left {P′ = S} !P⟶S) =
      case 6-1-3-2 !P⟶S
        return (const $ ∃ λ _ → _ × [ i ] _ ∼′ _)
        of λ where
        (inj₁ (P′ , P⟶P′ , S∼!P∣P′)) →
          ! (P ∣ Q)             ⟶⟨ replication (par-right (par-left P⟶P′)) ⟩ʳˡ
          ! (P ∣ Q) ∣ (P′ ∣ Q)  ∼⟨ left-lemma ⟩
          (! P ∣ P′) ∣ ! Q      ∼⟨ symmetric S∼!P∣P′ ∣-cong reflexive ⟩■
          S ∣ ! Q

        (inj₂ (refl , P′ , P″ , a , P⟶P′ , P⟶P″ , S∼!P∣P′∣P″)) →
          ! (P ∣ Q)                          [ τ ]⟶⟨ replication (par-τ (replication (par-right (par-left P⟶P′)))
                                                                        (par-left P⟶P″)) ⟩ʳˡ
          (! (P ∣ Q) ∣ (P′ ∣ Q)) ∣ (P″ ∣ Q)  ∼⟨ left-lemma ∣-cong′ reflexive ⟩
          ((! P ∣ P′) ∣ ! Q) ∣ (P″ ∣ Q)      ∼⟨ swap-in-the-middle ⟩
          ((! P ∣ P′) ∣ P″) ∣ (! Q ∣ Q)      ∼⟨ reflexive ∣-cong 6-1-2 ⟩
          ((! P ∣ P′) ∣ P″) ∣ ! Q            ∼⟨ symmetric S∼!P∣P′∣P″ ∣-cong reflexive ⟩■
          S ∣ ! Q

    rl (par-right {Q′ = S} !Q⟶S) =
      case 6-1-3-2 !Q⟶S
        return (const $ ∃ λ _ → _ × [ i ] _ ∼′ _)
        of λ where
        (inj₁ (Q′ , Q⟶Q′ , S∼!Q∣Q′)) →
          ! (P ∣ Q)             ⟶⟨ replication (par-right (par-right Q⟶Q′)) ⟩ʳˡ
          ! (P ∣ Q) ∣ (P ∣ Q′)  ∼⟨ right-lemma ⟩
          ! P ∣ (! Q ∣ Q′)      ∼⟨ reflexive ∣-cong symmetric S∼!Q∣Q′ ⟩■
          ! P ∣ S

        (inj₂ (refl , Q′ , Q″ , a , Q⟶Q′ , Q⟶Q″ , S∼!Q∣Q′∣Q″)) →
          ! (P ∣ Q)                          [ τ ]⟶⟨ replication (par-τ (replication (par-right (par-right Q⟶Q′)))
                                                                        (par-right Q⟶Q″)) ⟩ʳˡ
          (! (P ∣ Q) ∣ (P ∣ Q′)) ∣ (P ∣ Q″)  ∼⟨ right-lemma ∣-cong′ reflexive ⟩
          (! P ∣ (! Q ∣ Q′)) ∣ (P ∣ Q″)      ∼⟨ swap-in-the-middle ⟩
          (! P ∣ P) ∣ ((! Q ∣ Q′) ∣ Q″)      ∼⟨ 6-1-2 ∣-cong reflexive ⟩
          ! P ∣ ((! Q ∣ Q′) ∣ Q″)            ∼⟨ reflexive ∣-cong symmetric S∼!Q∣Q′∣Q″ ⟩■
          ! P ∣ S

    rl (par-τ {P′ = S} {Q′ = S′} !P⟶S !Q⟶S′) =
      case 6-1-3-2 !P⟶S ,′ 6-1-3-2 !Q⟶S′ of λ where
        (inj₁ (P′ , P⟶P′ , S∼!P∣P′) ,
         inj₁ (Q′ , Q⟶Q′ , S′∼!Q∣Q′)) →
          ! (P ∣ Q)                          [ τ ]⟶⟨ replication (par-τ (replication (par-right (par-left P⟶P′)))
                                                                                     (par-right Q⟶Q′)) ⟩ʳˡ
          (! (P ∣ Q) ∣ (P′ ∣ Q)) ∣ (P ∣ Q′)  ∼⟨ left-lemma ∣-cong′ reflexive ⟩
          ((! P ∣ P′) ∣ ! Q) ∣ (P ∣ Q′)      ∼⟨ swap-in-the-middle ⟩
          ((! P ∣ P′) ∣ P) ∣ (! Q ∣ Q′)      ∼⟨ swap-rightmost ∣-cong reflexive ⟩
          ((! P ∣ P) ∣ P′) ∣ (! Q ∣ Q′)      ∼⟨ (6-1-2 ∣-cong reflexive) ∣-cong reflexive ⟩
          (! P ∣ P′) ∣ (! Q ∣ Q′)            ∼⟨ symmetric (S∼!P∣P′ ∣-cong S′∼!Q∣Q′) ⟩■
          S ∣ S′

        (inj₁ _ , inj₂ (() , _))
        (inj₂ (() , _) , _)

  6-2-17-1′ : ∀ {i P Q} → [ i ] ! (P ∣ Q) ∼′ ! P ∣ ! Q
  force 6-2-17-1′ = 6-2-17-1

mutual

  6-2-17-2 : ∀ {i P Q} → [ i ] ! (P ⊕ Q) ∼ ! P ∣ ! Q
  6-2-17-2 {i} {P} {Q} = ⟨ lr , rl ⟩
    where
    left-lemma = λ {R : Proc ∞} →
      ! (P ⊕ Q) ∣ R    ∼⟨ 6-2-17-2′ {i = i} ∣-cong′ reflexive ⟩
      (! P ∣ ! Q) ∣ R  ∼⟨ swap-rightmost ⟩■
      (! P ∣ R) ∣ ! Q

    right-lemma = λ {R : Proc ∞} →
      ! (P ⊕ Q) ∣ R    ∼⟨ 6-2-17-2′ {i = i} ∣-cong′ reflexive ⟩
      (! P ∣ ! Q) ∣ R  ∼⟨ symmetric ∣-assoc ⟩■
      ! P ∣ (! Q ∣ R)

    τ-lemma₁ = λ {P′ P″ : Proc ∞} →
      (! (P ⊕ Q) ∣ P′) ∣ P″    ∼⟨ left-lemma ∣-cong′ reflexive ⟩
      ((! P ∣ P′) ∣ ! Q) ∣ P″  ∼⟨ swap-rightmost ⟩■
      ((! P ∣ P′) ∣ P″) ∣ ! Q

    τ-lemma₂ = λ {P′ Q′ : Proc ∞} →
      (! (P ⊕ Q) ∣ P′) ∣ Q′    ∼⟨ left-lemma ∣-cong′ reflexive ⟩
      ((! P ∣ P′) ∣ ! Q) ∣ Q′  ∼⟨ symmetric ∣-assoc ⟩■
      (! P ∣ P′) ∣ (! Q ∣ Q′)

    τ-lemma₃ = λ {Q′ Q″ : Proc ∞} →
      (! (P ⊕ Q) ∣ Q′) ∣ Q″    ∼⟨ right-lemma ∣-cong′ reflexive ⟩
      (! P ∣ (! Q ∣ Q′)) ∣ Q″  ∼⟨ symmetric ∣-assoc ⟩■
      ! P ∣ ((! Q ∣ Q′) ∣ Q″)

    lr : ∀ {R μ} →
         ! (P ⊕ Q) [ μ ]⟶ R →
         ∃ λ S → ! P ∣ ! Q [ μ ]⟶ S × [ i ] R ∼′ S
    lr {R} tr =
      case 6-1-3-2 tr
        return (const $ ∃ λ _ → _ × [ i ] _ ∼′ _)
        of λ where

        (inj₁ (P′ , sum-left P⟶P′ , R∼![P⊕Q]∣P′)) →
          R                 ∼⟨ R∼![P⊕Q]∣P′ ⟩
          ! (P ⊕ Q) ∣ P′    ∼⟨ left-lemma ⟩■
          (! P ∣ P′) ∣ ! Q  ⟵⟨ par-left (replication (par-right P⟶P′)) ⟩
          ! P        ∣ ! Q

        (inj₁ (Q′ , sum-right Q⟶Q′ , R∼![P⊕Q]∣Q′)) →
          R                 ∼⟨ R∼![P⊕Q]∣Q′ ⟩
          ! (P ⊕ Q) ∣ Q′    ∼⟨ right-lemma ⟩■
          ! P ∣ (! Q ∣ Q′)  ⟵⟨ par-right (replication (par-right Q⟶Q′)) ⟩
          ! P ∣  ! Q

        (inj₂ ( refl , P′ , P″ , c
              , sum-left P⟶P′ , sum-left P⟶P″
              , R∼![P⊕Q]∣P′∣P″
              )) →
          R                        ∼⟨ R∼![P⊕Q]∣P′∣P″ ⟩
          (! (P ⊕ Q) ∣ P′) ∣ P″    ∼⟨ τ-lemma₁ ⟩■
          ((! P ∣ P′) ∣ P″) ∣ ! Q  [ τ ]⟵⟨ par-left (replication (par-τ (replication (par-right P⟶P′)) P⟶P″)) ⟩
          ! P ∣ ! Q

        (inj₂ ( refl , P′ , Q′ , c
              , sum-left P⟶P′ , sum-right Q⟶Q′
              , R∼![P⊕Q]∣P′∣Q′
              )) →
          R                        ∼⟨ R∼![P⊕Q]∣P′∣Q′ ⟩
          (! (P ⊕ Q) ∣ P′) ∣ Q′    ∼⟨ τ-lemma₂ ⟩■
          (! P ∣ P′) ∣ (! Q ∣ Q′)  [ τ ]⟵⟨ par-τ (replication (par-right P⟶P′))
                                                 (replication (par-right Q⟶Q′)) ⟩
          ! P ∣ ! Q

        (inj₂ ( refl , Q′ , P′ , c
              , sum-right Q⟶Q′ , sum-left P⟶P′
              , R∼![P⊕Q]∣Q′∣P′
              )) →
          R                        ∼⟨ R∼![P⊕Q]∣Q′∣P′ ⟩
          (! (P ⊕ Q) ∣ Q′) ∣ P′    ∼⟨ right-lemma ∣-cong′ reflexive ⟩
          (! P ∣ (! Q ∣ Q′)) ∣ P′  ∼⟨ swap-rightmost ⟩■
          (! P ∣ P′) ∣ (! Q ∣ Q′)  [ τ ]⟵⟨ par-τ′ (sym $ co-involutive c)
                                                  (replication (par-right P⟶P′))
                                                  (replication (par-right Q⟶Q′)) ⟩
          ! P ∣ ! Q

        (inj₂ ( refl , Q′ , Q″ , c
              , sum-right Q⟶Q′ , sum-right Q⟶Q″
              , R∼![P⊕Q]∣Q′∣Q″
              )) →
          R                        ∼⟨ R∼![P⊕Q]∣Q′∣Q″ ⟩
          (! (P ⊕ Q) ∣ Q′) ∣ Q″    ∼⟨ τ-lemma₃ ⟩■
          ! P ∣ ((! Q ∣ Q′) ∣ Q″)  [ τ ]⟵⟨ par-right (replication (par-τ (replication (par-right Q⟶Q′)) Q⟶Q″)) ⟩
          ! P ∣ ! Q

    rl : ∀ {S μ} →
         ! P ∣ ! Q [ μ ]⟶ S →
         ∃ λ R → ! (P ⊕ Q) [ μ ]⟶ R × [ i ] R ∼′ S
    rl (par-left {P′ = S} !P⟶S) =
      case 6-1-3-2 !P⟶S
        return (const $ ∃ λ _ → _ × [ i ] _ ∼′ _)
        of λ where
        (inj₁ (P′ , P⟶P′ , S∼!P∣P′)) →
          ! (P ⊕ Q)         ⟶⟨ replication (par-right (sum-left P⟶P′)) ⟩ʳˡ
          ! (P ⊕ Q) ∣ P′    ∼⟨ left-lemma ⟩
          (! P ∣ P′) ∣ ! Q  ∼⟨ symmetric S∼!P∣P′ ∣-cong reflexive ⟩■
          S ∣ ! Q

        (inj₂ (refl , P′ , P″ , a , P⟶P′ , P⟶P″ , S∼!P∣P′∣P″)) →
          ! (P ⊕ Q)                [ τ ]⟶⟨ replication (par-τ (replication (par-right (sum-left P⟶P′)))
                                                              (sum-left P⟶P″)) ⟩ʳˡ
          (! (P ⊕ Q) ∣ P′) ∣ P″    ∼⟨ τ-lemma₁ ⟩
          ((! P ∣ P′) ∣ P″) ∣ ! Q  ∼⟨ symmetric S∼!P∣P′∣P″ ∣-cong reflexive ⟩■
          S ∣ ! Q

    rl (par-right {Q′ = S} !Q⟶S) =
      case 6-1-3-2 !Q⟶S
        return (const $ ∃ λ _ → _ × [ i ] _ ∼′ _)
        of λ where
        (inj₁ (Q′ , Q⟶Q′ , S∼!Q∣Q′)) →
          ! (P ⊕ Q)         ⟶⟨ replication (par-right (sum-right Q⟶Q′)) ⟩ʳˡ
          ! (P ⊕ Q) ∣ Q′    ∼⟨ right-lemma ⟩
          ! P ∣ (! Q ∣ Q′)  ∼⟨ reflexive ∣-cong symmetric S∼!Q∣Q′ ⟩■
          ! P ∣ S

        (inj₂ (refl , Q′ , Q″ , a , Q⟶Q′ , Q⟶Q″ , S∼!Q∣Q′∣Q″)) →
          ! (P ⊕ Q)                [ τ ]⟶⟨ replication (par-τ (replication (par-right (sum-right Q⟶Q′)))
                                                              (sum-right Q⟶Q″)) ⟩ʳˡ
          (! (P ⊕ Q) ∣ Q′) ∣ Q″    ∼⟨ τ-lemma₃ ⟩
          ! P ∣ ((! Q ∣ Q′) ∣ Q″)  ∼⟨ reflexive ∣-cong symmetric S∼!Q∣Q′∣Q″ ⟩■
          ! P ∣ S

    rl (par-τ {P′ = S} {Q′ = S′} !P⟶S !Q⟶S′) =
      case 6-1-3-2 !P⟶S ,′ 6-1-3-2 !Q⟶S′ of λ where
        (inj₁ (P′ , P⟶P′ , S∼!P∣P′) ,
         inj₁ (Q′ , Q⟶Q′ , S′∼!Q∣Q′)) →
          ! (P ⊕ Q)                [ τ ]⟶⟨ replication (par-τ (replication (par-right (sum-left P⟶P′)))
                                                                                      (sum-right Q⟶Q′)) ⟩ʳˡ
          (! (P ⊕ Q) ∣ P′) ∣ Q′    ∼⟨ τ-lemma₂ ⟩
          (! P ∣ P′) ∣ (! Q ∣ Q′)  ∼⟨ symmetric (S∼!P∣P′ ∣-cong S′∼!Q∣Q′) ⟩■
          S ∣ S′

        (inj₁ _ , inj₂ (() , _))
        (inj₂ (() , _) , _)

  6-2-17-2′ : ∀ {i P Q} → [ i ] ! (P ⊕ Q) ∼′ ! P ∣ ! Q
  force 6-2-17-2′ = 6-2-17-2

6-2-17-3 : ∀ {P} → ! P ∣ ! P ∼ ! P
6-2-17-3 {P} =
  ! P ∣ ! P  ∼⟨ symmetric 6-2-17-2 ⟩
  ! (P ⊕ P)  ∼⟨ !-cong ⊕-idempotent ⟩■
  ! P

-- A result mentioned in the proof of 6.2.17 (4) in "Enhancements of
-- the bisimulation proof method".

6-2-17-4-lemma : ∀ {P Q μ} → ! P [ μ ]⟶ Q → Q ∼ ! P ∣ Q
6-2-17-4-lemma {P} {Q} !P⟶Q = case 6-1-3-2 !P⟶Q of λ where
  (inj₁ (P′ , P⟶P′ , Q∼!P∣P′)) →
    Q                 ∼⟨ Q∼!P∣P′ ⟩
    ! P ∣ P′          ∼⟨ symmetric 6-2-17-3 ∣-cong reflexive ⟩
    (! P ∣ ! P) ∣ P′  ∼⟨ symmetric ∣-assoc ⟩
    ! P ∣ (! P ∣ P′)  ∼⟨ reflexive ∣-cong symmetric Q∼!P∣P′ ⟩■
    ! P ∣ Q

  (inj₂ (_ , P′ , P″ , _ , P⟶P′ , P⟶P″ , Q∼!P∣P′∣P″)) →
    Q                        ∼⟨ Q∼!P∣P′∣P″ ⟩
    (! P ∣ P′) ∣ P″          ∼⟨ symmetric ∣-assoc ⟩
    ! P ∣ (P′ ∣ P″)          ∼⟨ symmetric 6-2-17-3 ∣-cong reflexive ⟩
    (! P ∣ ! P) ∣ (P′ ∣ P″)  ∼⟨ symmetric ∣-assoc ⟩
    ! P ∣ (! P ∣ (P′ ∣ P″))  ∼⟨ reflexive ∣-cong ∣-assoc ⟩
    ! P ∣ ((! P ∣ P′) ∣ P″)  ∼⟨ reflexive ∣-cong symmetric Q∼!P∣P′∣P″ ⟩■
    ! P ∣ Q

mutual

  6-2-17-4 : ∀ {P i} → [ i ] ! ! P ∼ ! P
  6-2-17-4 {P} {i} = ⟨ lr , rl ⟩
    where
    lemma = λ {Q μ} (!P⟶Q : ! P [ μ ]⟶ Q) →
      ! ! P ∣ Q  ∼⟨ 6-2-17-4′ {i = i} ∣-cong′ reflexive ⟩
      ! P ∣ Q    ∼⟨ symmetric (6-2-17-4-lemma !P⟶Q) ⟩■
      Q

    lr : ∀ {Q μ} →
         ! ! P [ μ ]⟶ Q →
         ∃ λ Q′ → ! P [ μ ]⟶ Q′ × [ i ] Q ∼′ Q′
    lr {Q} !!P⟶Q = case 6-1-3-2 !!P⟶Q of λ where
      (inj₁ (Q′ , !P⟶Q′ , Q∼!!P∣Q′)) →
          _
        , !P⟶Q′
        , (Q           ∼⟨ Q∼!!P∣Q′ ⟩
           ! ! P ∣ Q′  ∼⟨ lemma !P⟶Q′ ⟩■
           Q′)

      (inj₂ (refl , Q′ , Q″ , a , !P⟶Q′ , !P⟶Q″ , Q∼!!P∣Q′∣Q″)) →
        case 6-1-3-2 !P⟶Q″ of λ where
          (inj₂ (() , _))
          (inj₁ (Q‴ , P⟶Q‴ , Q″∼!P∣Q‴)) →
            let !P⟶Q′∣Q″ =
                  ! P      [ τ ]⟶⟨ replication (par-τ !P⟶Q′ P⟶Q‴) ⟩
                  Q′ ∣ Q‴
            in
            Q                          ∼⟨ Q∼!!P∣Q′∣Q″ ⟩
            (! ! P ∣ Q′) ∣ Q″          ∼⟨ reflexive ∣-cong Q″∼!P∣Q‴ ⟩
            (! ! P ∣ Q′) ∣ (! P ∣ Q‴)  ∼⟨ swap-in-the-middle ⟩
            (! ! P ∣ ! P) ∣ (Q′ ∣ Q‴)  ∼⟨ 6-1-2 ∣-cong reflexive ⟩
            ! ! P ∣ (Q′ ∣ Q‴)          ∼⟨ lemma !P⟶Q′∣Q″ ⟩■
            Q′ ∣ Q‴                    [ τ ]⟵⟨ !P⟶Q′∣Q″ ⟩
            ! P

    rl : ∀ {Q μ} →
         ! P [ μ ]⟶ Q →
         ∃ λ Q′ → ! ! P [ μ ]⟶ Q′ × [ i ] Q′ ∼′ Q
    rl {Q} !P⟶Q =
      ! ! P      ⟶⟨ replication (par-right !P⟶Q) ⟩ʳˡ
      ! ! P ∣ Q  ∼⟨ lemma !P⟶Q ⟩■
      Q

  6-2-17-4′ : ∀ {P i} → [ i ] ! ! P ∼′ ! P
  force 6-2-17-4′ = 6-2-17-4

------------------------------------------------------------------------
-- An example from "Coinduction All the Way Up" by Pous

module _ (a b : Name-with-kind) where

  A B C D : ∀ {i} → Proc i

  A = name a ∙ name b ∙ D
  B = name a ∙ name b ∙ C

  C = name (co a) · λ { .force → A ∣ C }
  D = name (co a) · λ { .force → B ∣ D }

  mutual

    A∼B : ∀ {i} → [ i ] A ∼ B
    A∼B = refl ∙-cong (refl ∙-cong symmetric C∼D)

    C∼D : ∀ {i} → [ i ] C ∼ D
    C∼D = refl ·-cong λ { .force → A∼B ∣-cong C∼D }

------------------------------------------------------------------------
-- Another example (not taken from Pous and Sangiorgi)

Restricted : Name → Proc ∞
Restricted a = ⟨ν a ⟩ (name (a , true) · λ { .force → ∅ })

Restricted∼∅ : ∀ {a} → Restricted a ∼ ∅
Restricted∼∅ =
  ⟨ (λ { (restriction x≢x action) → ⊥-elim (x≢x refl) })
  , (λ ())
  ⟩
