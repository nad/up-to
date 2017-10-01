------------------------------------------------------------------------
-- Up-to techniques, compatibility, size-preserving functions, and the
-- companion
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

-- The definitions below are parametrised by an indexed container.

open import Indexed-container

module Up-to {ℓ} {I : Set ℓ} (C : Container I I) where

open import Equality.Propositional
open import Logical-equivalence using (_⇔_)
open import Prelude

open import Bijection equality-with-J using (_↔_)
open import Function-universe equality-with-J as F hiding (id; _∘_)

open import Indexed-container.Combinators
  hiding (id; const) renaming (_∘_ to _⊚_)
open import Relation

------------------------------------------------------------------------
-- Up-to techniques

-- This definition of soundness is based on the definition of
-- "b-soundness" given by Pous and Sangiorgi in "Enhancements of the
-- bisimulation proof method", with the following differences:
--
-- * The property is stated for an indexed container rather than a
--   monotone function on a (particular) complete lattice.
--
-- * The extension ⟦ C ⟧ of the container C takes the place of b.
--
-- * The type-theoretic greatest fixpoint ν takes the place of a
--   set-theoretic greatest fixpoint.

Sound : Container I I → Set ℓ
Sound F = ν (C ⊚ F) ∞ ⊆ ν C ∞

-- A relation transformer F is an up-to technique if every relation R
-- that is contained in ⟦ C ⟧ (F R) is contained in ν C ∞.

Up-to-technique : Trans ℓ I → Set (lsuc ℓ)
Up-to-technique F = ∀ {R} → R ⊆ ⟦ C ⟧ (F R) → R ⊆ ν C ∞

-- The two definitions above are pointwise logically equivalent, if
-- the second one is restricted to containers (in a certain way).

Sound⇔ : ∀ F → Sound F ⇔ Up-to-technique ⟦ F ⟧
Sound⇔ F = record
  { to = λ sound {R} →

      R ⊆ ⟦ C ⟧ (⟦ F ⟧ R)  ↝⟨ ⊆-congʳ _ (_⇔_.from $ ⟦∘⟧↔ _ C) ⟩

      R ⊆ ⟦ C ⊚ F ⟧ R      ↝⟨ unfold (C ⊚ F) ⟩

      R ⊆ ν (C ⊚ F) ∞      ↝⟨ ⊆-congʳ _ sound ⟩□

      R ⊆ ν C ∞            □

  ; from = λ up-to → up-to (

      ν (C ⊚ F) ∞                  ⊆⟨ ν-out _ ⟩

      ⟦ C ⊚ F ⟧ (ν (C ⊚ F) ∞)      ⊆⟨ ⟦∘⟧↔ _ C ⟩∎

      ⟦ C ⟧ (⟦ F ⟧ (ν (C ⊚ F) ∞))  ∎)

  }

------------------------------------------------------------------------
-- Compatibility

-- Compatibility.
--
-- This definition corresponds to Pous and Sangiorgi's definition of
-- b-compatibility.

Compatible : Trans ℓ I → Set (lsuc ℓ)
Compatible F = ∀ R → F (⟦ C ⟧ R) ⊆ ⟦ C ⟧ (F R)

-- If F is monotone and compatible, and R is contained in ⟦ C ⟧ (F R),
-- then F ^ω R is a post-fixpoint of ⟦ C ⟧.
--
-- The proof of Pous and Sangiorgi's Theorem 6.3.9 contains a similar
-- result.

compatible→^ω-post-fixpoint :
  ∀ {F} →
  Monotone F → Compatible F →
  ∀ {R} → R ⊆ ⟦ C ⟧ (F R) → F ^ω R ⊆ ⟦ C ⟧ (F ^ω R)
compatible→^ω-post-fixpoint {F} mono comp {R = R} R⊆ = uncurry λ n →
  F ^[ n ] R              ⊆⟨ Fⁿ⊆∘F¹⁺ⁿ n ⟩
  ⟦ C ⟧ (F ^[ 1 + n ] R)  ⊆⟨ map C (1 + n ,_) ⟩∎
  ⟦ C ⟧ (F ^ω R)          ∎
  where
  Fⁿ⊆∘F¹⁺ⁿ : ∀ n → F ^[ n ] R ⊆ ⟦ C ⟧ (F ^[ suc n ] R)
  Fⁿ⊆∘F¹⁺ⁿ zero =
    R            ⊆⟨ R⊆ ⟩∎
    ⟦ C ⟧ (F R)  ∎
  Fⁿ⊆∘F¹⁺ⁿ (suc n) =
    F ^[ 1 + n ] R              ⊆⟨⟩
    F (F ^[ n ] R)              ⊆⟨ mono (Fⁿ⊆∘F¹⁺ⁿ n) ⟩
    F (⟦ C ⟧ (F ^[ 1 + n ] R))  ⊆⟨ comp _ ⟩∎
    ⟦ C ⟧ (F ^[ 2 + n ] R)      ∎

-- Monotone compatible functions are up-to techniques.
--
-- This is basically Pous and Sangiorgi's Theorem 6.3.9.

compatible→up-to :
  ∀ {F} → Monotone F → Compatible F → Up-to-technique F
compatible→up-to {F} mono comp {R = R} R⊆ =
  R       ⊆⟨ 0 ,_ ⟩
  F ^ω R  ⊆⟨ unfold C (compatible→^ω-post-fixpoint mono comp R⊆) ⟩∎
  ν C ∞   ∎

------------------------------------------------------------------------
-- Size-preserving functions (using sized types)

-- F is size-preserving if, for any relation R, if R is contained in
-- ν C i, then F R is contained in ν C i.

Size-preserving : Trans ℓ I → Set (lsuc ℓ)
Size-preserving F =
  ∀ {R : Rel ℓ I} {i} → R ⊆ ν C i → F R ⊆ ν C i

-- If the relation transformer F is size-preserving, then F is an
-- up-to technique.
--
-- On the other hand, up-to techniques are not necessarily
-- size-preserving, not even for monotone and extensive transformers,
-- see
-- Bisimilarity.Up-to.Counterexamples.∃monotone×extensive×up-to×¬size-preserving.
-- Thus the property of being size-preserving is less general than
-- that of being an up-to technique. However, the latter property is
-- not closed under composition (not even for monotone and extensive
-- transformers, see Bisimilarity.Up-to.Counterexamples.¬-∘-closure),
-- whereas the former property is (see ∘-closure below).

size-preserving→up-to :
  {F : Trans ℓ I} →
  Size-preserving F → Up-to-technique F
size-preserving→up-to {F} pres = size-preserving→up-to′
  where

  -- F is also size-preserving for ν′.

  pres′ : ∀ {R : Rel ℓ I} {i} → R ⊆ ν′ C i → F R ⊆ ν′ C i
  force (pres′ R⊆ν′ FRx) =
    pres (λ Rx′ → force (R⊆ν′ Rx′)) FRx

  size-preserving→up-to′ :
    ∀ {i} {R : Rel ℓ I} →
    R ⊆ ⟦ C ⟧ (F R) → R ⊆ ν C i
  size-preserving→up-to′ {i} {R} R⊆CFR =
    R               ⊆⟨ R⊆CFR ⟩
    ⟦ C ⟧ (F R)     ⊆⟨ map C (pres′ size-preserving→up-to″) ⟩
    ⟦ C ⟧ (ν′ C i)  ⊆⟨ id ⟩∎
    ν C i           ∎
    where
    size-preserving→up-to″ : R ⊆ ν′ C i
    force (size-preserving→up-to″ Rx) =
      size-preserving→up-to′ R⊆CFR Rx

-- If F is monotone, then Size-preserving F is logically equivalent to
-- a special case stating that, for any size i, ν C i should be a
-- pre-fixpoint of F.
--
-- Note that size-preserving relation transformers are not necessarily
-- monotone (or extensive), see
-- Bisimilarity.Up-to.Counterexamples.∃size-preserving×¬[monotone⊎extensive].
--
-- Furthermore there is a container C such that transformers F that
-- satisfy the property ∀ {i} → F (ν C i) ⊆ ν C i are not necessarily
-- up-to techniques for C, see
-- Bisimilarity.Up-to.Counterexamples.∃special-case-of-size-preserving×¬up-to.

monotone→⇔ :
  {F : Trans ℓ I} →
  Monotone F →
  Size-preserving F
    ⇔
  (∀ {i} → F (ν C i) ⊆ ν C i)
monotone→⇔ {F} F-mono = record
  { to   = λ pres {i} →
             F (ν C i)  ⊆⟨ pres id ⟩∎
             ν C i      ∎
  ; from = λ drop {R i} R⊆ν →
             F R        ⊆⟨ F-mono R⊆ν ⟩
             F (ν C i)  ⊆⟨ drop ⟩∎
             ν C i      ∎
  }

-- A special case of compatibility.

Compatible′ : Trans ℓ I → Set ℓ
Compatible′ F = ∀ {i} → F (⟦ C ⟧ (ν′ C i)) ⊆ ⟦ C ⟧ (F (ν′ C i))

-- Monotone transformers that satisfy the special case of
-- compatibility are size-preserving.

monotone→compatible′→size-preserving :
  ∀ {F} → Monotone F → Compatible′ F → Size-preserving F
monotone→compatible′→size-preserving {F} mono comp =
  _⇔_.from (monotone→⇔ mono) lemma
  where

  mutual

    lemma : ∀ {i} → F (ν C i) ⊆ ν C i
    lemma {i} =
      F (ν C i)           ⊆⟨⟩
      F (⟦ C ⟧ (ν′ C i))  ⊆⟨ comp ⟩
      ⟦ C ⟧ (F (ν′ C i))  ⊆⟨ map C lemma′ ⟩
      ⟦ C ⟧ (ν′ C i)      ⊆⟨ id ⟩∎
      ν C i               ∎

    lemma′ : ∀ {i} → F (ν′ C i) ⊆ ν′ C i
    force (lemma′ {i} Fν′x) {j = j} =
      lemma (mono (ν′ C i  ⊆⟨ (λ ν′y → force ν′y) ⟩∎
                   ν C j   ∎)
                  Fν′x)

-- Thus monotone, compatible transformers are size-preserving.

monotone→compatible→size-preserving :
  {F : Trans ℓ I} →
  Monotone F →
  Compatible F →
  Size-preserving F
monotone→compatible→size-preserving mono comp =
  monotone→compatible′→size-preserving mono (comp _)

-- Extensive, size-preserving transformers satisfy the special case of
-- compatibility.

extensive→size-preserving→compatible′ :
  ∀ {F} →
  Extensive F → Size-preserving F → Compatible′ F
extensive→size-preserving→compatible′ {F} extensive pres {i} =
  F (⟦ C ⟧ (ν′ C i))  ⊆⟨⟩
  F (ν C i)           ⊆⟨ pres id ⟩
  ν C i               ⊆⟨⟩
  ⟦ C ⟧ (ν′ C i)      ⊆⟨ map C (extensive _) ⟩∎
  ⟦ C ⟧ (F (ν′ C i))  ∎

-- For monotone and extensive transformers the special case of
-- compatibility is logically equivalent to being size-preserving.
--
-- However, size-preserving transformers are not necessarily
-- compatible, not even if they are monotone and extensive, see
-- Bisimilarity.Up-to.Counterexamples.∃monotone×extensive×size-preserving×¬compatible.
-- Thus the property of being size-preserving is more general than the
-- property of being compatible. However, it is more well-behaved than
-- Up-to-technique, because it is closed under composition (see
-- ∘-closure below).

monotone→extensive→size-preserving⇔compatible′ :
  ∀ {F} →
  Monotone F → Extensive F →
  Size-preserving F ⇔ Compatible′ F
monotone→extensive→size-preserving⇔compatible′ mono extensive = record
  { to   = extensive→size-preserving→compatible′ extensive
  ; from = monotone→compatible′→size-preserving mono
  }

-- The following four lemmas correspond to Pous and Sangiorgi's
-- Proposition 6.3.11.

-- The identity function is size-preserving.

id-size-preserving :
  Size-preserving id
id-size-preserving = id

-- If R is contained in ν C ∞, then const R is size-preserving.

const-size-preserving :
  {R : Rel ℓ I} →
  R ⊆ ν C ∞ →
  Size-preserving (const R)
const-size-preserving R⊆∼ _ = R⊆∼

-- If F and G are both size-preserving, then F ∘ G is also
-- size-preserving.

∘-closure :
  {F G : Trans ℓ I} →
  Size-preserving F →
  Size-preserving G →
  Size-preserving (F ∘ G)
∘-closure {F} {G} F-pres G-pres {R = R} {i = i} =
 R ⊆ ν C i        ↝⟨ G-pres ⟩
 G R ⊆ ν C i      ↝⟨ F-pres ⟩□
 F (G R) ⊆ ν C i  □

-- If F is a family of size-preserving transformers, then ⋃ lzero F is
-- also size-preserving.

⋃-closure :
  {A : Set ℓ} {F : A → Trans ℓ I} →
  (∀ a → Size-preserving (F a)) →
  Size-preserving (⋃ lzero F)
⋃-closure {F = F} pres {R = R} {i = i} =
  R ⊆ ν C i                        ↝⟨ (λ R⊆∼ {_} → uncurry λ a →

      F a R                              ⊆⟨ pres a (λ {_} → R⊆∼ {_}) ⟩∎
      ν C i                              ∎) ⟩□

  (λ b → ∃ λ a → F a R b) ⊆ ν C i  □

-- If F and G are both size-preserving, then
-- λ R → F R ∪ G R is also size-preserving.

∪-closure :
  {F G : Trans ℓ I} →
  Size-preserving F →
  Size-preserving G →
  Size-preserving (λ R → F R ∪ G R)
∪-closure {F} {G} F-pres G-pres {R = R} {i = i} =
  R ⊆ ν C i          ↝⟨ (λ R⊆∼ {_} → [ F-pres (R⊆∼ {_}) , G-pres (R⊆∼ {_}) ]) ⟩□
  F R ∪ G R ⊆ ν C i  □

------------------------------------------------------------------------
-- The companion

-- The companion.
--
-- The name comes from "Coinduction All the Way Up" by Pous, but this
-- definition is based on the one presented by Parrow and Weber in
-- "The Largest Respectful Function".

Companion : Trans ℓ I
Companion R o = ∀ {i} → R ⊆ ν C i → ν C i o

-- The companion is monotone.
--
-- This result corresponds to Lemma 2.13 in "The Largest Respectful
-- Function".

companion-monotone : Monotone Companion
companion-monotone R⊆S f S⊆ = f (S⊆ ∘ R⊆S)

-- The companion is size-preserving.

companion-size-preserving : Size-preserving Companion
companion-size-preserving {R} {i} R⊆ {o} =
  (∀ {i} → R ⊆ ν C i → ν C i o)  ↝⟨ (λ hyp → hyp R⊆) ⟩□
  ν C i o                        □

-- The companion is an up-to technique.

companion-up-to : Up-to-technique Companion
companion-up-to = size-preserving→up-to companion-size-preserving

-- Every size-preserving function is contained in the companion.

size-preserving⊆companion :
  ∀ {F} → Size-preserving F → ∀ R → F R ⊆ Companion R
size-preserving⊆companion {F} pres R {o} FR {i} =
  R ⊆ ν C i    ↝⟨ pres ⟩
  F R ⊆ ν C i  ↝⟨ (λ hyp → hyp FR) ⟩□
  ν C i o      □

-- Every "partial" fixpoint ν C i is a pre-fixpoint of the companion.

companion-ν⊆ν : ∀ {i} → Companion (ν C i) ⊆ ν C i
companion-ν⊆ν {i} =
  (∀ {j} → ν C i ⊆ ν C j → ν C j _)  ↝⟨ (λ hyp → hyp id) ⟩□
  ν C i _                            □

-- Some lemmas corresponding to Lemma 3.2 from "Coinduction All the
-- Way Up".

⟦⟧⊆companion : ∀ R → ⟦ C ⟧ R ⊆ Companion R
⟦⟧⊆companion R CR {i} =
  R ⊆ ν C i                ↝⟨ map C ⟩
  ⟦ C ⟧ R ⊆ ⟦ C ⟧ (ν C i)  ↝⟨ (λ hyp → hyp CR) ⟩
  ⟦ C ⟧ (ν C i) _          ↝⟨ ν-in _ ⟩□
  ν C i _                  □

id⊆companion : ∀ R → R ⊆ Companion R
id⊆companion R r {i} =
  R ⊆ ν C i  ↝⟨ (λ hyp → hyp r) ⟩□
  ν C i _    □

companion²⊆companion : ∀ R → Companion (Companion R) ⊆ Companion R
companion²⊆companion R CCR {i} =
  R ⊆ ν C i                        ↝⟨ companion-monotone ⟩
  Companion R ⊆ Companion (ν C i)  ↝⟨ companion-ν⊆ν ∘_ ⟩
  Companion R ⊆ ν C i              ↝⟨ CCR ⟩□
  ν C i _                          □

companion-idempotent :
  ∀ R {o} → Companion (Companion R) o ⇔ Companion R o
companion-idempotent R {o} = record
  { to   = companion²⊆companion R
  ; from = Companion R              ⊆⟨ companion-monotone (id⊆companion _) ⟩∎
           Companion (Companion R)  ∎
  }

-- The greatest fixpoint ν C ∞ is pointwise logically equivalent to
-- the companion applied to an empty relation.
--
-- This corresponds to Theorem 3.3 from "Coinduction All the Way Up".

ν⇔companion-⊥ : ∀ {o} → ν C ∞ o ⇔ Companion (λ _ → ⊥) o
ν⇔companion-⊥ {o} = record
  { to   = ν C ∞ o                                ↝⟨ (λ hyp {_} _ → hyp) ⟩□
           (∀ {i} → (λ _ → ⊥) ⊆ ν C i → ν C i o)  □
  ; from = (∀ {i} → (λ _ → ⊥) ⊆ ν C i → ν C i o)  ↝⟨ (λ hyp → hyp (λ ())) ⟩□
           ν C ∞ o                                □
  }

-- The companion applied to the greatest fixpoint ν C ∞ is pointwise
-- logically equivalent to the greatest fixpoint.
--
-- This corresponds to Corollary 3.4 from "Coinduction All the Way
-- Up".

companion-ν⇔ν : ∀ {o} → Companion (ν C ∞) o ⇔ ν C ∞ o
companion-ν⇔ν {o} = record
  { to   = companion-ν⊆ν
  ; from = ν C ∞                ⊆⟨ _⇔_.to ν⇔companion-⊥ ⟩
           Companion (λ _ → ⊥)  ⊆⟨ companion-monotone (λ ()) ⟩∎
           Companion (ν C ∞)    ∎
  }

-- Pous defines the companion in roughly the following way in
-- "Coinduction All the Way Up".
--
-- Note that this definition is large.

Companion′ : Rel ℓ I → Rel (lsuc ℓ) I
Companion′ R = λ x →
  ∃ λ (F : Trans ℓ I) → Monotone F × Compatible F × F R x

-- This variant of the companion is compatible (modulo size issues).
--
-- This corresponds to Lemma 3.2 from "Coinduction All the Way Up".

companion′-compatible :
  ∀ R → Companion′ (⟦ C ⟧ R) ⊆ ⟦ C ⟧ (Companion′ R)
companion′-compatible R {x} (F , mono , comp , FCR) =
                          $⟨ FCR ⟩
  F (⟦ C ⟧ R) x           ↝⟨ comp R ⟩
  ⟦ C ⟧ (F R) x           ↝⟨ map C (λ FR → F , (λ {_ _} → mono) , comp , FR) ⟩□
  ⟦ C ⟧ (Companion′ R) x  □

-- Pous' variant of the companion is monotone.

companion′-monotone : ∀ {R S} → R ⊆ S → Companion′ R ⊆ Companion′ S
companion′-monotone R⊆S =
  ∃-cong λ _ → ∃-cong λ mono → ∃-cong λ _ → mono R⊆S

-- Pous' variant of the companion is contained in Companion.

companion′⊆companion : ∀ {R} → Companion′ R ⊆ Companion R
companion′⊆companion {R} {o} =
  Companion′ R o                                 ↔⟨ ∃-cong (λ _ → Σ-assoc) ⟩
  (∃ λ F → (Monotone F × Compatible F) × F R o)  ↝⟨ ∃-cong (λ _ → uncurry monotone→compatible→size-preserving ×-cong id) ⟩
  (∃ λ F → Size-preserving F × F R o)            ↝⟨ (λ { (_ , pres , FR) → size-preserving⊆companion pres _ FR }) ⟩□
  Companion R o                                  □

-- The other direction holds iff Companion is compatible.
--
-- However, I don't know if this is provable (constructively).

companion-compatible⇔companion⊆companion′ :
  Compatible Companion ⇔ (∀ {R} → Companion R ⊆ Companion′ R)
companion-compatible⇔companion⊆companion′ = record
  { to   = λ comp  f → Companion , companion-monotone , comp , f
  ; from = λ below R →
             Companion (⟦ C ⟧ R)   ⊆⟨ below ⟩

             Companion′ (⟦ C ⟧ R)  ⊆⟨ (λ { (F , mono , comp , x) → (_$ x) (

                 F (⟦ C ⟧ R)            ⊆⟨ comp _ ⟩

                 ⟦ C ⟧ (F R)            ⊆⟨ map C (

                     F R                     ⊆⟨ (λ y → F , (λ {_ _} → mono) , comp , y) ⟩
                     Companion′ R            ⊆⟨ companion′⊆companion ⟩∎
                     Companion R             ∎) ⟩∎

                 ⟦ C ⟧ (Companion R)     ∎) }) ⟩∎

             ⟦ C ⟧ (Companion R)   ∎
  }

-- If "one half of f-symmetry" holds for R, for some involution f,
-- then the other half also holds.
--
-- (Pous mentions something similar in "Coinduction All the Way Up".)

other-half-of-symmetry :
  {f : I → I} →
  f ∘ f ≡ id →
  (R : Rel ℓ I) → R ∘ f ⊆ R → R ⊆ R ∘ f
other-half-of-symmetry {f} f-involution R R∘f⊆R =
  R          ⊆⟨ (λ {o} → subst (λ g → R (g o)) (sym f-involution)) ⟩
  R ∘ f ∘ f  ⊆⟨ R∘f⊆R ⟩∎
  R ∘ f      ∎

-- The results in the following module correspond to parts of
-- Proposition 7.1 in "Coinduction All the Way Up".

module _
  (D : Container I I)
  (f : I → I)
  (f-involution : f ∘ f ≡ id)
  (C⇔⟷D : ∀ {R : Rel ℓ I} {o} → ⟦ C ⟧ R o ⇔ ⟦ D ⊗ reindex f D ⟧ R o)
  where

  mutual

    ν-symmetric : ∀ {i} → ν C i ∘ f ⊆ ν C i
    ν-symmetric {i} =
      ν C i ∘ f                                          ⊆⟨⟩
      ⟦ C ⟧ (ν′ C i) ∘ f                                 ⊆⟨ _⇔_.to C⇔⟷D ⟩
      ⟦ D ⊗ reindex f D ⟧ (ν′ C i) ∘ f                   ⊆⟨ ⟦⊗⟧↔ _ D (reindex f D) ⟩
      ⟦ D ⟧ (ν′ C i) ∘ f ∩ ⟦ reindex f D ⟧ (ν′ C i) ∘ f  ⊆⟨ Σ-map id (⟦reindex⟧↔ _ D) ⟩
      ⟦ D ⟧ (ν′ C i) ∘ f ∩ ⟦ D ⟧ (ν′ C i ∘ f) ∘ f ∘ f    ⊆⟨ (λ {o} → Σ-map id (subst (λ g → ⟦ D ⟧ (ν′ C i ∘ f) (g o)) f-involution)) ⟩
      ⟦ D ⟧ (ν′ C i) ∘ f ∩ ⟦ D ⟧ (ν′ C i ∘ f)            ⊆⟨ Σ-map (map D (other-half-of-symmetry f-involution (ν′ C i) ν′-symmetric))
                                                                  (map D ν′-symmetric) ⟩
      ⟦ D ⟧ (ν′ C i ∘ f) ∘ f ∩ ⟦ D ⟧ (ν′ C i)            ⊆⟨ swap ⟩
      ⟦ D ⟧ (ν′ C i) ∩ ⟦ D ⟧ (ν′ C i ∘ f) ∘ f            ⊆⟨ Σ-map id (_⇔_.from (⟦reindex⟧↔ _ D)) ⟩
      ⟦ D ⟧ (ν′ C i) ∩ ⟦ reindex f D ⟧ (ν′ C i)          ⊆⟨ _⇔_.from (⟦⊗⟧↔ _ D (reindex f D)) ⟩
      ⟦ D ⊗ reindex f D ⟧ (ν′ C i)                       ⊆⟨ _⇔_.from C⇔⟷D ⟩
      ⟦ C ⟧ (ν′ C i)                                     ⊆⟨ id ⟩∎
      ν C i                                              ∎

    ν′-symmetric : ∀ {i} → ν′ C i ∘ f ⊆ ν′ C i
    force (ν′-symmetric x) = ν-symmetric (force x)

  companion-symmetric : ∀ {R} → Companion R ∘ f ⊆ Companion R
  companion-symmetric {R} {o} =
    Companion R (f o)                  ↔⟨⟩
    (∀ {i} → R ⊆ ν C i → ν C i (f o))  ↝⟨ (λ hyp {i} R⊆ν → ν-symmetric (hyp R⊆ν)) ⟩
    (∀ {i} → R ⊆ ν C i → ν C i o)      ↔⟨⟩
    Companion R o                      □

  symmetry-lemma :
    {R S : Rel ℓ I} →
    R ∘ f ⊆ R →
    R ⊆ ⟦ C ⟧ (Companion S) ⇔ R ⊆ ⟦ D ⟧ (Companion S)
  symmetry-lemma {R} {S} R-sym = record { to = to; from = from }
    where
    lemma = λ {o} →
      ⟦ C ⟧ (Companion S) o                                    ↝⟨ C⇔⟷D ⟩
      ⟦ D ⊗ reindex f D ⟧ (Companion S) o                      ↝⟨ ⟦⊗⟧↔ _ D (reindex f D) ⟩
      ⟦ D ⟧ (Companion S) o × ⟦ reindex f D ⟧ (Companion S) o  ↝⟨ ∃-cong (λ _ → ⟦reindex⟧↔ _ D) ⟩□
      ⟦ D ⟧ (Companion S) o × ⟦ D ⟧ (Companion S ∘ f) (f o)    □

    to : R ⊆ ⟦ C ⟧ (Companion S) → R ⊆ ⟦ D ⟧ (Companion S)
    to R⊆CCS =
      R                                                  ⊆⟨ R⊆CCS ⟩
      ⟦ C ⟧ (Companion S)                                ⊆⟨ _⇔_.to lemma ⟩
      ⟦ D ⟧ (Companion S) ∩ ⟦ D ⟧ (Companion S ∘ f) ∘ f  ⊆⟨ proj₁ ⟩∎
      ⟦ D ⟧ (Companion S)                                ∎

    from : R ⊆ ⟦ D ⟧ (Companion S) → R ⊆ ⟦ C ⟧ (Companion S)
    from R⊆DCS =
      R                                                  ⊆⟨ (λ x → x , x) ⟩
      R ∩ R                                              ⊆⟨ Σ-map id (other-half-of-symmetry f-involution R R-sym) ⟩
      R ∩ R ∘ f                                          ⊆⟨ Σ-map R⊆DCS R⊆DCS ⟩
      ⟦ D ⟧ (Companion S) ∩ ⟦ D ⟧ (Companion S) ∘ f      ⊆⟨ Σ-map id (map D (other-half-of-symmetry f-involution
                                                                               (Companion S) companion-symmetric)) ⟩
      ⟦ D ⟧ (Companion S) ∩ ⟦ D ⟧ (Companion S ∘ f) ∘ f  ⊆⟨ _⇔_.from lemma ⟩∎
      ⟦ C ⟧ (Companion S)                                ∎

-- Another conservative approximation of "up-to technique": being
-- below the companion. This notion was presented by Pous in
-- "Coinduction All the Way Up".

Below-the-companion : Trans ℓ I → Set (lsuc ℓ)
Below-the-companion F = ∀ R → F R ⊆ Companion R

-- A transformer is below the companion iff it is size-preserving.
--
-- This is a generalisation of the following result, which is based on
-- a proposition due to Pous and Rot.

⊆companion⇔size-preserving :
  ∀ {F} → Below-the-companion F ⇔ Size-preserving F
⊆companion⇔size-preserving {F} = record
  { to   = λ F⊆C {R} {i} R⊆ν →
             F R          ⊆⟨ F⊆C _ ⟩
             Companion R  ⊆⟨ (λ hyp → hyp R⊆ν) ⟩∎
             ν C i        ∎
  ; from = size-preserving⊆companion
  }

-- A monotone transformer F is below the companion iff, for all
-- sizes i, ν C i is a pre-fixpoint of F.
--
-- This corresponds roughly to Proposition 5.2 in "Companions,
-- Codensity and Causality" by Pous and Rot.

monotone→⊆companion⇔size-preserving :
  ∀ {F} →
  Monotone F →
  Below-the-companion F ⇔ (∀ {i} → F (ν C i) ⊆ ν C i)
monotone→⊆companion⇔size-preserving {F} mono =
  Below-the-companion F        ↝⟨ ⊆companion⇔size-preserving ⟩
  Size-preserving F            ↝⟨ monotone→⇔ mono ⟩□
  (∀ {i} → F (ν C i) ⊆ ν C i)  □
