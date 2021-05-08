------------------------------------------------------------------------
-- Up-to techniques, compatibility, size-preserving functions, and the
-- companion
------------------------------------------------------------------------

{-# OPTIONS --sized-types #-}

-- The definitions below are parametrised by an indexed container.

open import Prelude

open import Indexed-container

module Up-to {ℓ} {I : Type ℓ} (C : Container I I) where

open import Equality.Propositional
open import Logical-equivalence using (_⇔_)
open import Prelude.Size

open import Bijection equality-with-J using (_↔_)
open import Function-universe equality-with-J as F hiding (id; _∘_)
open import Function-universe.Size equality-with-J

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

Sound : Container I I → Type ℓ
Sound F = ν (C ⊚ F) ∞ ⊆ ν C ∞

-- A relation transformer F is a (sound) up-to technique if every
-- relation R that is contained in ⟦ C ⟧ (F R) is contained in ν C ∞.

Up-to-technique : Trans ℓ I → Type (lsuc ℓ)
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

Compatible : Trans ℓ I → Type (lsuc ℓ)
Compatible F = ∀ {R} → F (⟦ C ⟧ R) ⊆ ⟦ C ⟧ (F R)

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
    F (⟦ C ⟧ (F ^[ 1 + n ] R))  ⊆⟨ comp ⟩∎
    ⟦ C ⟧ (F ^[ 2 + n ] R)      ∎

-- Monotone compatible functions are up-to techniques.
--
-- This is basically Pous and Sangiorgi's Theorem 6.3.9.

monotone→compatible→up-to :
  ∀ {F} → Monotone F → Compatible F → Up-to-technique F
monotone→compatible→up-to {F} mono comp {R = R} R⊆ =
  R       ⊆⟨ 0 ,_ ⟩
  F ^ω R  ⊆⟨ unfold C (compatible→^ω-post-fixpoint mono comp R⊆) ⟩∎
  ν C ∞   ∎

------------------------------------------------------------------------
-- Size-preserving functions (using sized types)

-- F is size-preserving if, for any relation R, if R is contained in
-- ν C i, then F R is contained in ν C i.

Size-preserving : Trans ℓ I → Type (lsuc ℓ)
Size-preserving F = ∀ {R i} → R ⊆ ν C i → F R ⊆ ν C i

-- If a transformer is size-preserving, then it satisfies the
-- corresponding property for ν′, and vice versa.
--
-- Note that this proof uses the size successor function.

size-preserving⇔size-preserving′ :
  ∀ {F} → Size-preserving F ⇔ (∀ {R i} → R ⊆ ν′ C i → F R ⊆ ν′ C i)
force (_⇔_.to size-preserving⇔size-preserving′ pres R⊆ν′Ci x) =
  pres (λ y → force (R⊆ν′Ci y)) x
_⇔_.from size-preserving⇔size-preserving′ pres′ {i = i} R⊆ν′Ci x =
  force (pres′ {i = ssuc i} (λ x → λ { .force → R⊆ν′Ci x }) x)

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

size-preserving→up-to : ∀ {F} → Size-preserving F → Up-to-technique F
size-preserving→up-to {F} pres {R = R} R⊆CFR = helper
  where
  helper : ∀ {i} → R ⊆ ⟦ C ⟧ (ν′ C i)
  helper =
    map C (_⇔_.to size-preserving⇔size-preserving′
             pres (λ x → λ { .force → helper x })) ∘
    R⊆CFR

  -- An alternative implementation of helper which might be a bit
  -- easier to follow.

  helper′ : ∀ {i} → R ⊆ ν C i
  helper′ {i} =
    R               ⊆⟨ R⊆CFR ⟩
    ⟦ C ⟧ (F R)     ⊆⟨ map C (_⇔_.to size-preserving⇔size-preserving′
                                pres (λ x → λ { .force → helper′ x })) ⟩
    ⟦ C ⟧ (ν′ C i)  ⊆⟨ id ⟩∎
    ν C i           ∎

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
  ∀ {F} →
  Monotone F →
  Size-preserving F ⇔ (∀ {i} → F (ν C i) ⊆ ν C i)
monotone→⇔ mono = record
  { to   = λ pres       → pres id
  ; from = λ pres R⊆νCi → pres ∘ mono R⊆νCi
  }

-- A special case of compatibility.

Compatible′ : Trans ℓ I → Type ℓ
Compatible′ F = ∀ {i} → F (⟦ C ⟧ (ν′ C i)) ⊆ ⟦ C ⟧ (F (ν′ C i))

-- Monotone transformers that satisfy the special case of
-- compatibility are size-preserving.

monotone→compatible′→size-preserving :
  ∀ {F} → Monotone F → Compatible′ F → Size-preserving F
monotone→compatible′→size-preserving {F = F} mono comp =
  _⇔_.from (monotone→⇔ mono) helper
  where

  mutual

    helper : ∀ {i} → F (⟦ C ⟧ (ν′ C i)) ⊆ ⟦ C ⟧ (ν′ C i)
    helper = map C helper′ ∘ comp

    helper′ : ∀ {i} → F (ν′ C i) ⊆ ν′ C i
    force (helper′ x) = helper (mono (λ y → force y) x)

  -- A variant of helper that is perhaps a bit easier to follow.

  helper″ : ∀ {i} → F (ν C i) ⊆ ν C i
  helper″ {i} =
    F (ν C i)           ⊆⟨⟩
    F (⟦ C ⟧ (ν′ C i))  ⊆⟨ comp ⟩
    ⟦ C ⟧ (F (ν′ C i))  ⊆⟨ map C helper′ ⟩
    ⟦ C ⟧ (ν′ C i)      ⊆⟨ id ⟩∎
    ν C i               ∎

  -- This definition is definitionally equal to helper.

  helper″≡helper : (λ {i x} → helper″ {i = i} {x = x}) ≡ helper
  helper″≡helper = refl

-- Monotone, compatible transformers are size-preserving.

monotone→compatible→size-preserving :
  ∀ {F} → Monotone F → Compatible F → Size-preserving F
monotone→compatible→size-preserving mono comp =
  monotone→compatible′→size-preserving mono comp

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
  ∀ {F G} →
  Size-preserving F → Size-preserving G → Size-preserving (F ∘ G)
∘-closure F-pres G-pres = F-pres ∘ G-pres

private

  -- An alternative implementation of ∘-closure which might be a bit
  -- easier to follow.

  ∘-closure′ :
    ∀ {F G} →
    Size-preserving F → Size-preserving G → Size-preserving (F ∘ G)
  ∘-closure′ {F} {G} F-pres G-pres {R = R} {i = i} =
   R ⊆ ν C i        ↝⟨ G-pres ⟩
   G R ⊆ ν C i      ↝⟨ F-pres ⟩□
   F (G R) ⊆ ν C i  □

-- If F is a family of size-preserving transformers, then ⋃ lzero F is
-- also size-preserving.

⋃-closure :
  {A : Type ℓ} {F : A → Trans ℓ I} →
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
Companion R x = ∀ {i} → R ⊆ ν C i → ν C i x

-- Another conservative approximation of "up-to technique": being
-- below the companion. This notion was presented by Pous in
-- "Coinduction All the Way Up".

Below-the-companion : Trans ℓ I → Type (lsuc ℓ)
Below-the-companion F = ∀ {R} → F R ⊆ Companion R

-- A transformer is below the companion iff it is size-preserving.
--
-- This is a generalisation of the following result, which is based on
-- a proposition due to Pous and Rot.

below-the-companion⇔size-preserving :
  ∀ {F} → Below-the-companion F ⇔ Size-preserving F
below-the-companion⇔size-preserving {F} = record
  { to   = λ below R⊆νCi x → below x R⊆νCi
  ; from = λ pres x R⊆νCi  → pres R⊆νCi x
  }

-- A monotone transformer F is below the companion iff, for all
-- sizes i, ν C i is a pre-fixpoint of F.
--
-- This corresponds roughly to Proposition 5.2 in "Companions,
-- Codensity and Causality" by Pous and Rot.

monotone→below-the-companion⇔size-preserving :
  ∀ {F} →
  Monotone F →
  Below-the-companion F ⇔ (∀ {i} → F (ν C i) ⊆ ν C i)
monotone→below-the-companion⇔size-preserving {F} mono =
  Below-the-companion F        ↝⟨ below-the-companion⇔size-preserving ⟩
  Size-preserving F            ↝⟨ monotone→⇔ mono ⟩□
  (∀ {i} → F (ν C i) ⊆ ν C i)  □

-- The companion is size-preserving.

companion-size-preserving : Size-preserving Companion
companion-size-preserving =
  _⇔_.to below-the-companion⇔size-preserving id

-- The companion is monotone.
--
-- This result corresponds to Lemma 2.13 in "The Largest Respectful
-- Function".

companion-monotone : Monotone Companion
companion-monotone R⊆S f S⊆νCi = f (S⊆νCi ∘ R⊆S)

-- A preservation lemma.

companion-cong :
  ∀ {k R S} →
  Extensionality? ⌊ k ⌋-sym ℓ ℓ →
  (∀ {x} → R x ↝[ ⌊ k ⌋-sym ] S x) →
  (∀ {x} → Companion R x ↝[ ⌊ k ⌋-sym ] Companion S x)
companion-cong {k} {R} {S} ext R↝S {x} =
  (∀ {i} → R ⊆ ν C i → ν C i x)  ↝⟨ implicit-∀-size-cong (lower-extensionality? ⌊ k ⌋-sym _ lzero ext) (→-cong ext (⊆-cong ext R↝S F.id) F.id) ⟩□
  (∀ {i} → S ⊆ ν C i → ν C i x)  □

-- The companion is an up-to technique.

companion-up-to : Up-to-technique Companion
companion-up-to = size-preserving→up-to companion-size-preserving

-- The following four lemmas correspond to parts of Lemma 3.2 from
-- "Coinduction All the Way Up".

-- The identity function is below the companion.

id-below : Below-the-companion id
id-below x f = f x

private

  -- An alternative implementation that might be a bit easier to
  -- follow.

  id-below′ : Below-the-companion id
  id-below′ {R = R} {x = x} Rx {i} =
    R ⊆ ν C i  ↝⟨ (λ f → f Rx) ⟩□
    ν C i x    □

-- ⟦ C ⟧ is below the companion.

⟦⟧-below : Below-the-companion ⟦ C ⟧
⟦⟧-below x = ν-in C ∘ (λ f → f x) ∘ map C

private

  -- An alternative implementation that might be a bit easier to
  -- follow.

  ⟦⟧-below′ : Below-the-companion ⟦ C ⟧
  ⟦⟧-below′ {R = R} {x = x} CR {i} =
    R ⊆ ν C i                ↝⟨ map C ⟩
    ⟦ C ⟧ R ⊆ ⟦ C ⟧ (ν C i)  ↝⟨ (λ f → f CR) ⟩
    ⟦ C ⟧ (ν C i) x          ↝⟨ ν-in C ⟩□
    ν C i x                  □

-- The companion composed with itself is below the companion.

companion∘companion-below : Below-the-companion (Companion ∘ Companion)
companion∘companion-below =
  _⇔_.from below-the-companion⇔size-preserving
    (∘-closure companion-size-preserving companion-size-preserving)

-- The companion is idempotent (in a certain sense).

companion-idempotent :
  ∀ R {x} → Companion (Companion R) x ⇔ Companion R x
companion-idempotent R = record
  { to   = companion∘companion-below
  ; from = Companion R              ⊆⟨ companion-monotone id-below ⟩∎
           Companion (Companion R)  ∎
  }

-- An example illustrating how some of the lemmas above can be used:
-- If F is below the companion, then ⟦ C ⟧ ∘ F is below
-- Companion ∘ Companion, which is below the companion.

below-the-companion-example :
  ∀ {F} → Below-the-companion F → Below-the-companion (⟦ C ⟧ ∘ F)
below-the-companion-example {F} =
  F Below Companion                          ↝⟨ ∘-cong₂ companion-monotone ⟦⟧-below ⟩
  (⟦ C ⟧ ∘ F) Below (Companion ∘ Companion)  ↝⟨ (λ below {_ _} → companion∘companion-below ∘ below {_}) ⟩□
  (⟦ C ⟧ ∘ F) Below Companion                □
  where
  _Below_ : Trans ℓ I → Trans ℓ I → Type (lsuc ℓ)
  F Below G = ∀ {R} → F R ⊆ G R

  ∘-cong₂ : ∀ {F₁ F₂ G₁ G₂ : Trans ℓ I} →
            Monotone F₂ →
            F₁ Below F₂ → G₁ Below G₂ → (F₁ ∘ G₁) Below (F₂ ∘ G₂)
  ∘-cong₂ {F₁} {F₂} {G₁} {G₂} F₂-mono F₁⊆F₂ G₁⊆G₂ {R} =
    F₁ (G₁ R)  ⊆⟨ F₁⊆F₂ ⟩
    F₂ (G₁ R)  ⊆⟨ F₂-mono G₁⊆G₂ ⟩∎
    F₂ (G₂ R)  ∎

-- The greatest fixpoint ν C ∞ is pointwise logically equivalent to
-- the companion applied to an empty relation.
--
-- This corresponds to Theorem 3.3 from "Coinduction All the Way Up".

ν⇔companion-⊥ : ∀ {x} → ν C ∞ x ⇔ Companion (λ _ → ⊥) x
ν⇔companion-⊥ {x} = record
  { to   = λ x _ → x
  ; from = λ f → f (λ ())
  }

-- Every "partial" fixpoint ν C i is a pre-fixpoint of the companion.

companion-ν⊆ν : ∀ {i} → Companion (ν C i) ⊆ ν C i
companion-ν⊆ν {i} =
  (∀ {j} → ν C i ⊆ ν C j → ν C j _)  ↝⟨ (λ hyp → hyp id) ⟩□
  ν C i _                            □

-- Every "partial" fixpoint ν′ C i is a pre-fixpoint of the companion.

companion-ν′⊆ν′ : ∀ {i} → Companion (ν′ C i) ⊆ ν′ C i
force (companion-ν′⊆ν′ hyp) =
  companion-ν⊆ν (companion-monotone (λ x → force x) hyp)

-- The companion applied to the greatest fixpoint ν C ∞ is pointwise
-- logically equivalent to the greatest fixpoint.
--
-- This corresponds to Corollary 3.4 from "Coinduction All the Way
-- Up".

companion-ν⇔ν : ∀ {x} → Companion (ν C ∞) x ⇔ ν C ∞ x
companion-ν⇔ν {x} = record
  { to   = companion-ν⊆ν
  ; from = ν C ∞                ⊆⟨ _⇔_.to ν⇔companion-⊥ ⟩
           Companion (λ _ → ⊥)  ⊆⟨ companion-monotone (λ ()) ⟩∎
           Companion (ν C ∞)    ∎
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
  R          ⊆⟨ (λ {x} → subst (λ g → R (g x)) (sym f-involution)) ⟩
  R ∘ f ∘ f  ⊆⟨ R∘f⊆R ⟩∎
  R ∘ f      ∎

-- The results in the following module are based on Proposition 7.1 in
-- "Coinduction All the Way Up".

module _
  (D : Container I I)
  (f : I → I)
  (f-involution : f ∘ f ≡ id)
  (C⇔⟷D : ∀ {R : Rel ℓ I} {x} → ⟦ C ⟧ R x ⇔ ⟦ D ⊗ reindex f D ⟧ R x)
  where

  mutual

    ν-symmetric : ∀ {i} → ν C i ∘ f ⊆ ν C i
    ν-symmetric {i} =
      ν C i ∘ f                                          ⊆⟨⟩
      ⟦ C ⟧ (ν′ C i) ∘ f                                 ⊆⟨ _⇔_.to C⇔⟷D ⟩
      ⟦ D ⊗ reindex f D ⟧ (ν′ C i) ∘ f                   ⊆⟨ ⟦⊗⟧↔ _ D (reindex f D) ⟩
      ⟦ D ⟧ (ν′ C i) ∘ f ∩ ⟦ reindex f D ⟧ (ν′ C i) ∘ f  ⊆⟨ Σ-map id (⟦reindex⟧↔ _ D) ⟩
      ⟦ D ⟧ (ν′ C i) ∘ f ∩ ⟦ D ⟧ (ν′ C i ∘ f) ∘ f ∘ f    ⊆⟨ (λ {x} → Σ-map id (subst (λ g → ⟦ D ⟧ (ν′ C i ∘ f) (g x)) f-involution)) ⟩
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
  companion-symmetric {R} {x} =
    Companion R (f x)                  ↔⟨⟩
    (∀ {i} → R ⊆ ν C i → ν C i (f x))  ↝⟨ (λ hyp R⊆ν → ν-symmetric (hyp R⊆ν)) ⦂ (_ → (∀ {i} → R ⊆ ν C i → ν C i x)) ⟩
    (∀ {i} → R ⊆ ν C i → ν C i x)      ↔⟨⟩
    Companion R x                      □

  symmetry-lemma :
    {R S : Rel ℓ I} →
    R ∘ f ⊆ R →
    R ⊆ ⟦ C ⟧ (Companion S) ⇔ R ⊆ ⟦ D ⟧ (Companion S)
  symmetry-lemma {R} {S} R-sym = record { to = to; from = from }
    where
    lemma = λ {x} →
      ⟦ C ⟧ (Companion S) x                                    ↝⟨ C⇔⟷D ⟩
      ⟦ D ⊗ reindex f D ⟧ (Companion S) x                      ↝⟨ ⟦⊗⟧↔ _ D (reindex f D) ⟩
      ⟦ D ⟧ (Companion S) x × ⟦ reindex f D ⟧ (Companion S) x  ↝⟨ ∃-cong (λ _ → ⟦reindex⟧↔ _ D) ⟩□
      ⟦ D ⟧ (Companion S) x × ⟦ D ⟧ (Companion S ∘ f) (f x)    □

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

-- Pous defines the companion in roughly the following way in
-- "Coinduction All the Way Up".
--
-- Note that this definition is large.

Companion₁ : Rel ℓ I → Rel (lsuc ℓ) I
Companion₁ R x = ∃ λ (F : Trans ℓ I) → Monotone F × Compatible F × F R x

-- Pous' variant of the companion is compatible (modulo size issues).
--
-- This corresponds to Lemma 3.2 from "Coinduction All the Way Up".

companion₁-compatible :
  ∀ R → Companion₁ (⟦ C ⟧ R) ⊆ ⟦ C ⟧ (Companion₁ R)
companion₁-compatible R {x} (F , mono , comp , FCR) =
                          $⟨ FCR ⟩
  F (⟦ C ⟧ R) x           ↝⟨ comp ⟩
  ⟦ C ⟧ (F R) x           ↝⟨ map C (λ FR → F , (λ {_ _} → mono) , (λ {_ _} → comp) , FR) ⟩□
  ⟦ C ⟧ (Companion₁ R) x  □

-- Pous' variant of the companion is monotone.

companion₁-monotone : ∀ {R S} → R ⊆ S → Companion₁ R ⊆ Companion₁ S
companion₁-monotone R⊆S =
  ∃-cong λ _ → ∃-cong λ mono → ∃-cong λ _ → mono R⊆S

-- Pous' variant of the companion is contained in Companion.

companion₁⊆companion : ∀ {R} → Companion₁ R ⊆ Companion R
companion₁⊆companion (F , mono , comp , x) =
  _⇔_.from below-the-companion⇔size-preserving
    (monotone→compatible→size-preserving mono comp) x

-- The other direction holds iff Companion is compatible.
--
-- However, I don't know if Companion is provably compatible (in
-- predicative, constructive type theory).

companion-compatible⇔companion⊆companion₁ :
  Compatible Companion ⇔ (∀ {R} → Companion R ⊆ Companion₁ R)
companion-compatible⇔companion⊆companion₁ = record
  { to   = λ comp f → (Companion , companion-monotone , comp , f)
  ; from = λ below f →
             let (F , mono , comp , FCR) = below f
             in map C ((λ FR → companion₁⊆companion (F , mono , comp , FR)) ⦂
                       (_ → Companion _ _))
                      (comp FCR)
  }
  where
  -- An alternative implementation of the from component which might
  -- be a bit easier to follow.

  from′ : (∀ {R} → Companion R ⊆ Companion₁ R) → Compatible Companion
  from′ below {R = R} =
    Companion (⟦ C ⟧ R)      ⊆⟨ below ⟩

    Companion₁ (⟦ C ⟧ R)     ⊆⟨ (λ { (F , mono , comp , x) → (_$ x) (

        F (⟦ C ⟧ R)               ⊆⟨ comp ⟩

        ⟦ C ⟧ (F R)               ⊆⟨ map C (

            F R                        ⊆⟨ (λ y → F , (λ {_ _} → mono) , (λ {_ _} → comp) , y) ⟩
            Companion₁ R               ⊆⟨ companion₁⊆companion ⟩∎
            Companion R                ∎) ⟩∎

        ⟦ C ⟧ (Companion R)        ∎) }) ⟩∎

    ⟦ C ⟧ (Companion R)      ∎

-- Assumptions used by companion-compatible below.

record Companion-compatible-assumptions : Type (lsuc ℓ) where
  field
    -- A strong form of excluded middle, not compatible with
    -- univalence.

    excluded-middle : (P : Type ℓ) → Dec P

  -- The type i < j means that i is a smaller size than j, i ≣ j means
  -- that i is equal to j, and i ≤ j means that i is smaller than or
  -- equal to j.

  infix 4 _<_ _≣_ _≤_

  _<_ : Size → Size → Type
  _<_ = λ i j → Σ (Size< j in-type) λ { k → record { size = i } ≡ k }

  _≣_ : Size → Size → Type
  _≣_ = λ i j →
    _≡_ {A = Size in-type} (record { size = i }) (record { size = j })

  _≤_ : Size → Size → Type
  _≤_ = λ i j → i < j ⊎ i ≣ j

  -- Successor sizes: Sizes i for which there is a size j < i such
  -- that every size k < i satisfies k ≤ j.

  Successor : Size → Type
  Successor i = ∃ λ (j : Size< i in-type) → (k : Size< i) → k ≤ size j

  field
    -- If i is not smaller than or equal to j, then j is smaller
    -- than i.

    ≰→> : ∀ {i j} → ¬ i ≤ j → j < i

    -- If a predicate from a certain class of predicates is satisfied
    -- for all sizes smaller than i, but not for i itself, then i is a
    -- successor size.

    is-successor :
      {R : Rel ℓ I} →
      let P = λ i → R ⊆ ν C i in
      ∀ i →
      ((j : Size< i) → P j) →
      ¬ P i →
      Successor i

    -- Size elimination. A very similar elimination principle can at
    -- the time of writing be implemented in Agda, but Andreas Abel
    -- has suggested that this implementation should not be allowed.

    size-elim :
      (P : Size → Type ℓ) →
      (∀ i → ((j : Size< i) → P j) → P i) →
      ∀ i → P i

  -- A variant of excluded-middle.

  excluded-middle₀ : (P : Type) → Dec P
  excluded-middle₀ P =
    ⊎-map lower (_∘ lift) $ excluded-middle (↑ ℓ P)

  -- "Not for all" implies "exists not".

  ¬∀→∃¬ : {A : Type} {P : A → Type ℓ} →
          ¬ (∀ x → P x) → ∃ λ x → ¬ P x
  ¬∀→∃¬ {P = P} ¬∀ = case excluded-middle (∃ λ x → ¬ P x) of λ where
    (inj₁ ∃¬P)  → ∃¬P
    (inj₂ ¬∃¬P) → ⊥-elim (¬∀ λ x → case excluded-middle (P x) of λ where
      (inj₁ Px)  → Px
      (inj₂ ¬Px) → ⊥-elim (¬∃¬P (x , ¬Px)))

  -- Given the assumptions above every pair of sizes must be related
  -- by either _<_, _≡_, or flip _<_. However, note that all three
  -- relations hold for ∞ and ∞, so we do not get a law of trichotomy.

  compare : ∀ i j → i < j ⊎ i ≣ j ⊎ j < i
  compare i j = case excluded-middle₀ (i < j) of λ where
    (inj₁ i<j) → inj₁ i<j
    (inj₂ i≮j) → case excluded-middle₀ (i ≣ j) of λ where
      (inj₁ i≡j) → inj₂ (inj₁ i≡j)
      (inj₂ i≢j) → inj₂ (inj₂ (≰→> [ i≮j , i≢j ]))

-- Given certain assumptions one can prove that the companion is
-- compatible. (The proof is based on that of Theorem 2.14 in Parrow
-- and Weber's "The Largest Respectful Function".) However, I don't
-- know if these assumptions are consistent with the variant of Agda
-- that is used in this development. I discussed the assumptions with
-- Andreas Abel and Andrea Vezzosi. Some potential problems came up in
-- the discussion:
--
-- * The fact that ∞ : Size< ∞ could perhaps lead to some kind of
--   problem.
--
-- * The assumptions make it possible to define functions that give
--   completely different results for different sizes (assuming that
--   there is more than one size).

companion-compatible :
  Companion-compatible-assumptions → Compatible Companion
companion-compatible assumptions {R} = case lemma R of λ where

    (inj₁ R⊆νC) →
      Companion (⟦ C ⟧ R)  ⊆⟨ _$ map C (λ Rx → λ { .force → R⊆νC Rx }) ⟩
      ν C ∞                ⊆⟨ map C ((λ ν′C∞x _ → force ν′C∞x) ⦂ (_ → Companion _ _)) ⟩∎
      ⟦ C ⟧ (Companion R)  ∎

    (inj₂ (1+i , (i , <1+i→≤i) , <1+i→R⊆νC , R⊈νC[1+i])) →

      let CR⊆νC[1+i] =
            ⟦ C ⟧ R               ⊆⟨ map C (<1+i→R⊆νC (size i)) ⟩
            ⟦ C ⟧ (ν C (size i))  ⊆⟨ map C (λ x → λ { .force {j} → cast (<1+i→≤i j) x }) ⟩∎
            ν C (size 1+i)        ∎

          νCi⊆CompanionR =
            ν C (size i)                                              ⊆⟨ (λ hyp → λ { j≤i → cast j≤i hyp }) ⟩
            (λ x → ∀ {j} → j ≤ size i → ν C j x)                      ⊆⟨ (λ hyp → λ { (j , refl) → hyp (<1+i→≤i (size j)) }) ⟩
            (λ x → ∀ {j} → j < size 1+i → ν C j x)                    ⊆⟨ (λ hyp → λ { j<1+i _ → hyp j<1+i }) ⟩
            (λ x → ∀ {j} → j < size 1+i → R ⊆ ν C j → ν C j x)        ⊆⟨ (λ hyp → λ { 1+i≰j → hyp (≰→> 1+i≰j) }) ⟩
            (λ x → ∀ {j} → ¬ size 1+i ≤ j → R ⊆ ν C j → ν C j x)      ⊆⟨ (λ hyp → λ { {j} → [ (λ 1+i≤j R⊆νCj →
                                                                                                 ⊥-elim $ R⊈νC[1+i] (
                R                                                                                  ⊆⟨ (λ {x} → R⊆νCj {x}) ⟩
                ν C j                                                                              ⊆⟨ cast 1+i≤j ⟩∎
                ν C (size 1+i)                                                                     ∎))
                                                                                            , hyp
                                                                                            ] }) ⟩
            (λ x → ∀ {j} → Dec (size 1+i ≤ j) → R ⊆ ν C j → ν C j x)  ⊆⟨ (λ hyp → λ { {_} → hyp (excluded-middle₀ _) }) ⟩
            (λ x → ∀ {j} → R ⊆ ν C j → ν C j x)                       ⊆⟨ id ⟩∎
            Companion R                                               ∎

          ν′C[1+i]⊆νCi : ν′ C (size 1+i) ⊆ ν C (size i)
          ν′C[1+i]⊆νCi {x} y =
            let y′ : (j : Size< (size 1+i)) → ν C j x
                y′ = λ { j → y .force {j = j} }
            in y′ (size i)
      in
      Companion (⟦ C ⟧ R)      ⊆⟨ (λ c → c {i = size 1+i} CR⊆νC[1+i]) ⟩
      ν C (size 1+i)           ⊆⟨⟩
      ⟦ C ⟧ (ν′ C (size 1+i))  ⊆⟨ map C ν′C[1+i]⊆νCi ⟩
      ⟦ C ⟧ (ν C (size i))     ⊆⟨ map C νCi⊆CompanionR ⟩∎
      ⟦ C ⟧ (Companion R)      ∎

  where
  open Companion-compatible-assumptions assumptions

  cast : ∀ {j k} → j ≤ k → ν C k ⊆ ν C j
  cast (inj₁ (_ , refl)) x = x
  cast (inj₂ refl)       x = x

  lemma :
    ∀ R → (∀ {i} → R ⊆ ν C i)
            ⊎
          ∃ λ i → Successor (size i) ×
                  ((j : Size< (size i)) → R ⊆ ν C j) ×
                  ¬ R ⊆ ν C (size i)
  lemma R =
    case excluded-middle (∀ {i} → R ⊆ ν C i) of
      ⊎-map id
        (¬ (∀ {i} → R ⊆ ν C i)                          ↝⟨ (λ hyp₁ hyp₂ → hyp₁ λ { {i} → hyp₂ {i = record { size = i }} }) ⟩

         ¬ (∀ {i} → R ⊆ ν C (size i))                   ↝⟨ (λ hyp → ¬∀→∃¬ {P = λ _ → _ ⊆ _} (λ ∀iR⊆νCi → hyp λ {i} → ∀iR⊆νCi i)) ⟩

         (∃ λ i → ¬ R ⊆ ν C (size i))                   ↝⟨ (λ (i , R⊈νCi) →
                                                              size-elim
                                                                (λ i → ¬ R ⊆ ν C i → _)
                                                                (λ i ind-hyp R⊈νCi → case excluded-middle
                                                                                            ((j : Size< i in-type) → R ⊆ ν C (size j))
                                                                                     of λ where
                                                                     (inj₁ ∀<R⊆νC)  → record { size = i }
                                                                                    , (λ { j → ∀<R⊆νC (record { size = j }) })
                                                                                    , R⊈νCi
                                                                     (inj₂ ¬∀<R⊆νC) → let j , R⊈νCj = ¬∀→∃¬ ¬∀<R⊆νC
                                                                                      in ind-hyp (size j) R⊈νCj)
                                                                (size i) R⊈νCi) ⟩
         (∃ λ i → ((j : Size< (size i)) → R ⊆ ν C j) ×
                  ¬ R ⊆ ν C (size i))                   ↝⟨ (λ { (i , hyp) → (i , uncurry (is-successor (size i)) hyp , hyp) }) ⟩□

         (∃ λ i → Successor (size i) ×
                  ((j : Size< (size i)) → R ⊆ ν C j) ×
                  ¬ R ⊆ ν C (size i))                   □)
