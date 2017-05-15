------------------------------------------------------------------------
-- Up-to techniques
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

-- The definitions below are parametrised by an indexed container.

open import Indexed-container

module Up-to {ℓ} {I : Set ℓ} (C : Container I I) where

open import Equality.Propositional
open import Logical-equivalence using (_⇔_)
open import Prelude

open import Function-universe equality-with-J hiding (id; _∘_)

open import Relation

------------------------------------------------------------------------
-- General results

-- A relation transformer F is an up-to technique if every relation R
-- that is contained in ⟦ C ⟧ (F R) is contained in ν C ∞.
--
-- This is roughly what Pous and Sangiorgi refer to as b-soundness in
-- "Enhancements of the bisimulation proof method", with b
-- corresponding to ⟦ C ⟧.

Up-to-technique : Trans ℓ I → Set (lsuc ℓ)
Up-to-technique F = ∀ {R} → R ⊆ ⟦ C ⟧ (F R) → R ⊆ ν C ∞

-- Compatibility.
--
-- This definition corresponds to Pous and Sangiorgi's definition of
-- b-compatibility.

Compatible : Trans ℓ I → Set (lsuc ℓ)
Compatible F = ∀ R → F (⟦ C ⟧ R) ⊆ ⟦ C ⟧ (F R)

-- Monotone compatible functions are up-to techniques.
--
-- This is basically Pous and Sangiorgi's Theorem 6.3.9.

module _
  {F    : Trans ℓ I}
  (mono : Monotone F)
  (comp : Compatible F)
  where

  private

    -- Repeated composition of a function with itself.

    infix 10 _^[_]_

    _^[_]_ : ∀ {a} {A : Set a} → (A → A) → ℕ → A → A
    f ^[ zero  ] x = x
    f ^[ suc n ] x = f (f ^[ n ] x)

    module _ (R : Rel ℓ I) (R-prog : R ⊆ ⟦ C ⟧ (F R)) where

      -- A lemma.

      Fⁿ⊆Step∘F¹⁺ⁿ : ∀ n → F ^[ n ] R ⊆ ⟦ C ⟧ (F ^[ suc n ] R)
      Fⁿ⊆Step∘F¹⁺ⁿ zero =
        R            ⊆⟨ R-prog ⟩∎
        ⟦ C ⟧ (F R)  ∎
      Fⁿ⊆Step∘F¹⁺ⁿ (suc n) =
        F ^[ 1 + n ] R              ⊆⟨⟩
        F (F ^[ n ] R)              ⊆⟨ mono (Fⁿ⊆Step∘F¹⁺ⁿ n) ⟩
        F (⟦ C ⟧ (F ^[ 1 + n ] R))  ⊆⟨ comp _ ⟩∎
        ⟦ C ⟧ (F ^[ 2 + n ] R)      ∎

      -- An analogue of ⋃ₙ Fⁿ(R).

      F^ωR : Rel ℓ I
      F^ωR pq = ∃ λ n → (F ^[ n ] R) pq

      -- F^ωR is a bisimulation.

      F^ωR-bisim : F^ωR ⊆ ⟦ C ⟧ F^ωR
      F^ωR-bisim = uncurry λ n →
        (F ^[ n ] R              ⊆⟨ Fⁿ⊆Step∘F¹⁺ⁿ n ⟩
         ⟦ C ⟧ (F ^[ 1 + n ] R)  ⊆⟨ map C (1 + n ,_) ⟩∎
         ⟦ C ⟧ F^ωR              ∎)

  compatible→up-to : Up-to-technique F
  compatible→up-to {R = R} R-prog =
    R              ⊆⟨ 0 ,_ ⟩
    F^ωR R R-prog  ⊆⟨ unfold C (F^ωR-bisim R R-prog) ⟩∎
    ν C ∞          ∎

-- F is size-preserving if, for any relation R, if R is contained in
-- ν C i, then F R is contained in ν C i.

Size-preserving : Trans ℓ I → Set (lsuc ℓ)
Size-preserving F =
  ∀ {R : Rel ℓ I} {i} → R ⊆ ν C i → F R ⊆ ν C i

-- If the relation transformer F is size-preserving, then F is an
-- up-to technique.
--
-- On the other hand, up-to techniques are not necessarily
-- size-preserving, not even for monotone transformers, see
-- Bisimilarity.Up-to.Counterexamples.¬monotone→up-to→size-preserving.
-- Thus the property of being size-preserving is less general than
-- that of being an up-to technique. However, the latter property is
-- not closed under composition (not even for monotone transformers,
-- see Bisimilarity.Up-to.Counterexamples.¬-∘-closure), whereas the
-- former property is (see ∘-closure below).

module _
  {F    : Trans ℓ I}
  (pres : Size-preserving F)
  where

  private

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

  size-preserving→up-to : Up-to-technique F
  size-preserving→up-to = size-preserving→up-to′

-- If F is monotone, then Size-preserving F is logically equivalent to
-- a special case stating that, for any size i, ν C i should be a
-- pre-fixpoint of F.
--
-- Note that size-preserving relation transformers are not necessarily
-- monotone, see
-- Bisimilarity.Up-to.Counterexamples.¬size-preserving→monotone.

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

-- A corollary of size-preserving→up-to and monotone→⇔.

size-preserving→up-to′ :
  {F : Trans ℓ I} →
  Monotone F →
  (∀ {i} → F (ν C i) ⊆ ν C i) →
  Up-to-technique F
size-preserving→up-to′ {F} mono =
  (∀ {i} → F (ν C i) ⊆ ν C i)  ↝⟨ _⇔_.from (monotone→⇔ mono) ⟩
  Size-preserving F            ↝⟨ size-preserving→up-to ⟩□
  Up-to-technique F            □

-- Monotone, compatible transformers are size-preserving.
--
-- On the other hand size-preserving transformers are not necessarily
-- compatible, not even if they are monotone, see
-- Bisimilarity.Up-to.Counterexamples.¬monotone→size-preserving→compatible.
-- Thus the property of being size-preserving is more general than the
-- property of being compatible. However, it is more well-behaved than
-- Up-to-technique, because it is closed under composition (see
-- ∘-closure below).

monotone→compatible→size-preserving :
  {F : Trans ℓ I} →
  Monotone F →
  Compatible F →
  Size-preserving F
monotone→compatible→size-preserving {F} mono comp =
  _⇔_.from (monotone→⇔ mono) lemma
  where

  mutual

    lemma : ∀ {i} → F (ν C i) ⊆ ν C i
    lemma {i} =
      F (ν C i)           ⊆⟨⟩
      F (⟦ C ⟧ (ν′ C i))  ⊆⟨ comp _ ⟩
      ⟦ C ⟧ (F (ν′ C i))  ⊆⟨ map C lemma′ ⟩
      ⟦ C ⟧ (ν′ C i)      ⊆⟨ id ⟩∎
      ν C i               ∎

    lemma′ : ∀ {i} → F (ν′ C i) ⊆ ν′ C i
    force (lemma′ {i} Fν′x) {j = j} =
      lemma (mono (ν′ C i  ⊆⟨ (λ ν′y → force ν′y) ⟩∎
                   ν C j   ∎)
                  Fν′x)

-- The following four lemmas correspond to Pous and Sangiorgi's
-- Proposition 6.3.11 (except that they state the fourth one for
-- arbitrary instead of binary unions).

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
