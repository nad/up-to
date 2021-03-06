------------------------------------------------------------------------
-- Unary and binary relations
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module Relation where

open import Equality.Propositional
open import Prelude

open import Bijection equality-with-J as Bijection using (_↔_)
open import Equality.Decision-procedures equality-with-J
import Equality.Groupoid equality-with-J as EG
open import Function-universe equality-with-J hiding (id; _∘_)
open import Groupoid equality-with-J

-- Unary relations.

Rel : ∀ {ℓ₁} ℓ₂ → Type ℓ₁ → Type (ℓ₁ ⊔ lsuc ℓ₂)
Rel ℓ A = A → Type ℓ

-- Homogeneous binary relations.

Rel₂ : ∀ {ℓ₁} ℓ₂ → Type ℓ₁ → Type (ℓ₁ ⊔ lsuc ℓ₂)
Rel₂ ℓ A = Rel ℓ (A × A)

-- One kind of unary relation transformer.

Trans : ∀ {a} ℓ → Type a → Type (a ⊔ lsuc ℓ)
Trans ℓ A = Rel ℓ A → Rel ℓ A

-- One kind of binary relation transformer.

Trans₂ : ∀ {a} ℓ → Type a → Type (a ⊔ lsuc ℓ)
Trans₂ ℓ A = Trans ℓ (A × A)

-- The converse of a binary relation.

infixr 10 _⁻¹

_⁻¹ : ∀ {a ℓ} {A : Type a} → Rel₂ ℓ A → Rel₂ ℓ A
R ⁻¹ = R ∘ swap

-- Composition of binary relations.

infixr 9 _⊙_

_⊙_ : ∀ {a ℓ₁ ℓ₂} {A : Type a} →
      Rel₂ ℓ₁ A → Rel₂ ℓ₂ A → Rel₂ (a ⊔ ℓ₁ ⊔ ℓ₂) A
(R ⊙ S) (x , z) = ∃ λ y → R (x , y) × S (y , z)

-- Composition of a relation with itself, with the base case as a
-- parameter.

composition : ∀ {a} {A : Type a} →
              Rel₂ a A → Rel₂ a A → ℕ → Rel₂ a A
composition R S zero    = R
composition R S (suc n) = S ⊙ composition R S n

-- Composition of a binary relation with itself, with the relation
-- itself as the base case.

infix 10 _^^[1+_]

_^^[1+_] : ∀ {a} {A : Type a} →
           Rel₂ a A → ℕ → Rel₂ a A
R ^^[1+ n ] = composition R R n

-- Composition of a binary relation with itself, with equality as the
-- base case.

infix 10 _^^_

_^^_ : ∀ {a} {A : Type a} →
       Rel₂ a A → ℕ → Rel₂ a A
R ^^ n = composition (uncurry _≡_) R n

-- Intersection of relations.

infixr 8 _∩_

_∩_ : ∀ {a ℓ₁ ℓ₂} {A : Type a} →
      Rel ℓ₁ A → Rel ℓ₂ A → Rel (ℓ₁ ⊔ ℓ₂) A
R ∩ S = λ x → R x × S x

-- Union of relations.

infixr 7 _∪_

_∪_ : ∀ {a ℓ₁ ℓ₂} {A : Type a} →
      Rel ℓ₁ A → Rel ℓ₂ A → Rel (ℓ₁ ⊔ ℓ₂) A
R ∪ S = λ x → R x ⊎ S x

-- Reflexive closure of binary relations.

_⁼ : ∀ {a ℓ} {A : Type a} →
     Rel₂ ℓ A → Rel₂ (a ⊔ ℓ) A
R ⁼ = R ∪ uncurry _≡_

-- Transitive closure of binary relations.

_⁺ : ∀ {a} {A : Type a} →
     Rel₂ a A → Rel₂ a A
(R ⁺) x = ∃ λ n → (R ^^[1+ n ]) x

-- Reflexive transitive closure of binary relations.

_* : ∀ {a} {A : Type a} →
     Rel₂ a A → Rel₂ a A
(R *) x = ∃ λ n → (R ^^ n) x

-- Repeated composition of a function with itself.

infix 10 _^[_]_

_^[_]_ : ∀ {a} {A : Type a} → (A → A) → ℕ → A → A
f ^[ zero  ] x = x
f ^[ suc n ] x = f (f ^[ n ] x)

-- Unions of families of relation transformers.

⋃ : ∀ {a b} ℓ {A : Type a} {B : Type b} →
    (A → Trans (a ⊔ ℓ) B) → Trans (a ⊔ ℓ) B
⋃ _ F R = λ b → ∃ λ a → F a R b

-- An analogue of ⋃ₙ Fⁿ.

infix 10 _^ω_

_^ω_ : ∀ {a ℓ} {A : Type a} → Trans ℓ A → Trans ℓ A
_^ω_ F = ⋃ _ (F ^[_]_)

-- Relation containment.

infix 4 _⊆_

_⊆_ : ∀ {a ℓ₁ ℓ₂} {A : Type a} →
      Rel ℓ₁ A → Rel ℓ₂ A → Type (a ⊔ ℓ₁ ⊔ ℓ₂)
R ⊆ S = ∀ {x} → R x → S x

-- "Equational" reasoning combinators.

infix  -1 finally-⊆
infixr -2 _⊆⟨_⟩_ _⊆⟨⟩_

_⊆⟨_⟩_ : ∀ {a p q r} {A : Type a}
         (P : Rel p A) {Q : Rel q A} {R : Rel r A} →
         P ⊆ Q → Q ⊆ R → P ⊆ R
_ ⊆⟨ P⊆Q ⟩ Q⊆R = Q⊆R ∘ P⊆Q

_⊆⟨⟩_ : ∀ {a p q} {A : Type a}
        (P : Rel p A) {Q : Rel q A} →
        P ⊆ Q → P ⊆ Q
_ ⊆⟨⟩ P⊆Q = P⊆Q

finally-⊆ : ∀ {a p q} {A : Type a}
            (P : Rel p A) (Q : Rel q A) →
            P ⊆ Q → P ⊆ Q
finally-⊆ _ _ P⊆Q = P⊆Q

syntax finally-⊆ P Q P⊆Q = P ⊆⟨ P⊆Q ⟩∎ Q ∎

-- Preservation lemmas for _⊆_.

infix 4 _⊆-cong-→_

⊆-cong :
  ∀ {k a r₁ r₂ s₁ s₂} {A : Type a}
    {R₁ : Rel r₁ A} {S₁ : Rel s₁ A}
    {R₂ : Rel r₂ A} {S₂ : Rel s₂ A} →
  Extensionality? ⌊ k ⌋-sym (a ⊔ r₁ ⊔ r₂) (r₁ ⊔ r₂ ⊔ s₁ ⊔ s₂) →
  (∀ {x} → R₁ x ↝[ ⌊ k ⌋-sym ] R₂ x) →
  (∀ {x} → S₁ x ↝[ ⌊ k ⌋-sym ] S₂ x) →
  R₁ ⊆ S₁ ↝[ ⌊ k ⌋-sym ] R₂ ⊆ S₂
⊆-cong {k} {a} {r₁} {r₂} ext R₁↝R₂ S₁↝S₂ =
  implicit-∀-cong
    (lower-extensionality? ⌊ k ⌋-sym (r₁ ⊔ r₂) lzero ext) $
  →-cong (lower-extensionality? ⌊ k ⌋-sym a (r₁ ⊔ r₂) ext)
         R₁↝R₂ S₁↝S₂

_⊆-cong-→_ :
  ∀ {a r₁ r₂ s₁ s₂} {A : Type a}
    {R₁ : Rel r₁ A} {S₁ : Rel s₁ A}
    {R₂ : Rel r₂ A} {S₂ : Rel s₂ A} →
  R₂ ⊆ R₁ → S₁ ⊆ S₂ → R₁ ⊆ S₁ → R₂ ⊆ S₂
R₂→R₁ ⊆-cong-→ S₁→S₂ = implicit-∀-cong _ $ →-cong-→ R₂→R₁ S₁→S₂

⊆-congʳ :
  ∀ {k a r s₁ s₂} {A : Type a}
    {R : Rel r A} {S₁ : Rel s₁ A} {S₂ : Rel s₂ A} →
  Extensionality? k (a ⊔ r) (r ⊔ s₁ ⊔ s₂) →
  (∀ {x} → S₁ x ↝[ k ] S₂ x) →
  R ⊆ S₁ ↝[ k ] R ⊆ S₂
⊆-congʳ {k} {a} {r} ext S₁↝S₂ =
  implicit-∀-cong (lower-extensionality? k r lzero ext) $
  ∀-cong (lower-extensionality? k a r ext) λ _ →
  S₁↝S₂

-- Relation containment (_⊆_) is not antisymmetric (with respect to
-- propositional equality) if the index type is inhabited.

⊆-not-antisymmetric :
  ∀ {ℓ x} {X : Type x} →
  X →
  ¬ ({R S : Rel ℓ X} → R ⊆ S → S ⊆ R → R ≡ S)
⊆-not-antisymmetric {ℓ} {X = X} x antisym = Bool.true≢false true≡false
  where
  R S : Rel ℓ X
  R = λ _ → ↑ _ ⊤
  S = λ _ → ↑ _ Bool

  R≡S : R ≡ S
  R≡S = antisym (λ _ → lift true) _

  ⊤≡Bool : ↑ _ ⊤ ≡ ↑ _ Bool
  ⊤≡Bool = cong (_$ x) R≡S

  ⊤↔Bool : ⊤ ↔ Bool
  ⊤↔Bool =
    ⊤         ↝⟨ inverse Bijection.↑↔ ⟩
    ↑ _ ⊤     ↝⟨ ≡⇒↝ _ ⊤≡Bool ⟩
    ↑ _ Bool  ↝⟨ Bijection.↑↔ ⟩□
    Bool      □

  true≡false : true ≡ false
  true≡false =
    true                                   ≡⟨ sym $ _↔_.right-inverse-of ⊤↔Bool _ ⟩
    _↔_.to ⊤↔Bool (_↔_.from ⊤↔Bool true)   ≡⟨⟩
    _↔_.to ⊤↔Bool tt                       ≡⟨⟩
    _↔_.to ⊤↔Bool (_↔_.from ⊤↔Bool false)  ≡⟨ _↔_.right-inverse-of ⊤↔Bool _ ⟩∎
    false                                  ∎

-- Monotonicity of relation transformers.

Monotone :
  ∀ {a ℓ} {A : Type a} →
  Trans ℓ A → Type (a ⊔ lsuc ℓ)
Monotone F = ∀ {R S} → R ⊆ S → F R ⊆ F S

-- A relation transformer is extensive if the input is always
-- contained in the output.

Extensive : ∀ {ℓ} {I : Type ℓ} → Trans ℓ I → Type (lsuc ℓ)
Extensive G = ∀ R → R ⊆ G R

-- A definition that turns into a notion of symmetry if the first
-- argument is instantiated with the swap function. In that case this
-- definition is similar to one of those given by Pous and Sangiorgi
-- in Section 6.3.4.1 of "Enhancements of the bisimulation proof
-- method".

Symmetric : ∀ {ℓ} {I : Type ℓ} → (I → I) → Trans ℓ I → Type (lsuc ℓ)
Symmetric f F = ∀ R → F (R ∘ f) ⊆ F R ∘ f

-- If f is an involution, then the inclusion in Symmetric f F holds
-- also in the other direction.

involution→other-symmetry :
  ∀ {ℓ} {I : Type ℓ} (F : Trans ℓ I) {f : I → I} →
  f ∘ f ≡ id → Symmetric f F → ∀ R → F R ∘ f ⊆ F (R ∘ f)
involution→other-symmetry F {f} inv symm R =
  F R ∘ f            ⊆⟨ (λ {x} → subst (λ g → F (R ∘ g) (f x)) (sym inv)) ⟩
  F (R ∘ f ∘ f) ∘ f  ⊆⟨ symm _ ⟩
  F (R ∘ f) ∘ f ∘ f  ⊆⟨ (λ {x} → subst (λ g → F (R ∘ f) (g x)) inv) ⟩∎
  F (R ∘ f)          ∎

-- Composition is associative.

⊙-assoc : ∀ {a ℓ₁ ℓ₂ ℓ₃} {A : Type a} →
          (R₁ : Rel₂ ℓ₁ A) {R₂ : Rel₂ ℓ₂ A} (R₃ : Rel₂ ℓ₃ A) →
          ∀ p → (R₁ ⊙ (R₂ ⊙ R₃)) p ↔ ((R₁ ⊙ R₂) ⊙ R₃) p
⊙-assoc R₁ {R₂} R₃ (a , d) =
  (∃ λ b → R₁ (a , b) × ∃ λ c → R₂ (b , c) × R₃ (c , d))    ↝⟨ ∃-cong (λ _ → ∃-comm) ⟩
  (∃ λ b → ∃ λ c → R₁ (a , b) × R₂ (b , c) × R₃ (c , d))    ↝⟨ ∃-comm ⟩
  (∃ λ c → ∃ λ b → R₁ (a , b) × R₂ (b , c) × R₃ (c , d))    ↝⟨ ∃-cong (λ _ → ∃-cong λ _ → Σ-assoc) ⟩
  (∃ λ c → ∃ λ b → (R₁ (a , b) × R₂ (b , c)) × R₃ (c , d))  ↝⟨ ∃-cong (λ _ → Σ-assoc) ⟩□
  (∃ λ c → (∃ λ b → R₁ (a , b) × R₂ (b , c)) × R₃ (c , d))  □

-- Several forms of composition preserve several kinds of functions.

⊙-cong :
  ∀ {k a r₁ r₂ s₁ s₂} {A : Type a} →
    {R₁ : Rel₂ r₁ A} {R₂ : Rel₂ r₂ A} →
    {S₁ : Rel₂ s₁ A} {S₂ : Rel₂ s₂ A} →
  (∀ p → R₁ p ↝[ k ] R₂ p) →
  (∀ p → S₁ p ↝[ k ] S₂ p) →
  ∀ p → (R₁ ⊙ S₁) p ↝[ k ] (R₂ ⊙ S₂) p
⊙-cong {R₁ = R₁} {R₂} {S₁} {S₂} R₁↝R₂ S₁↝S₂ (x , z) =
  (∃ λ y → R₁ (x , y) × S₁ (y , z))  ↝⟨ ∃-cong (λ _ → R₁↝R₂ _ ×-cong S₁↝S₂ _) ⟩□
  (∃ λ y → R₂ (x , y) × S₂ (y , z))  □

composition-cong :
  ∀ {k a} {A : Type a} {R₁ R₂ S₁ S₂ : Rel₂ a A} →
  (∀ p → R₁ p ↝[ k ] R₂ p) →
  (∀ p → S₁ p ↝[ k ] S₂ p) →
  ∀ n p → composition R₁ S₁ n p ↝[ k ] composition R₂ S₂ n p
composition-cong R₁↝R₂ S₁↝S₂ = λ where
  zero    → R₁↝R₂
  (suc n) → ⊙-cong S₁↝S₂ (composition-cong R₁↝R₂ S₁↝S₂ n)

^^[1+]-cong :
  ∀ {k a} {A : Type a} {R₁ R₂ : Rel₂ a A} →
  (∀ p → R₁ p ↝[ k ] R₂ p) →
  ∀ n p → (R₁ ^^[1+ n ]) p ↝[ k ] (R₂ ^^[1+ n ]) p
^^[1+]-cong R₁↝R₂ = composition-cong R₁↝R₂ R₁↝R₂

^^-cong :
  ∀ {k a} {A : Type a} {R₁ R₂ : Rel₂ a A} →
  (∀ p → R₁ p ↝[ k ] R₂ p) →
  ∀ n p → (R₁ ^^ n) p ↝[ k ] (R₂ ^^ n) p
^^-cong R₁↝R₂ = composition-cong (λ _ → _ □) R₁↝R₂

⁺-cong :
  ∀ {k a} {A : Type a} {R₁ R₂ : Rel₂ a A} →
  (∀ p → R₁ p ↝[ k ] R₂ p) →
  ∀ p → (R₁ ⁺) p ↝[ k ] (R₂ ⁺) p
⁺-cong R₁↝R₂ p = ∃-cong λ n → ^^[1+]-cong R₁↝R₂ n p

*-cong :
  ∀ {k a} {A : Type a} {R₁ R₂ : Rel₂ a A} →
  (∀ p → R₁ p ↝[ k ] R₂ p) →
  ∀ p → (R₁ *) p ↝[ k ] (R₂ *) p
*-cong R₁↝R₂ p = ∃-cong λ n → ^^-cong R₁↝R₂ n p

-- Two lemmas relating composition and _⊙_.

composition-⊙-comm :
  ∀ {k a} {A : Type a} {R S : Rel₂ a A} →
  (∀ p → (R ⊙ S) p ↝[ k ] (S ⊙ R) p) →
  ∀ n p → (composition R S n ⊙ S) p ↝[ k ] (S ⊙ composition R S n) p
composition-⊙-comm             hyp zero    = hyp
composition-⊙-comm {R = R} {S} hyp (suc n) = λ p →
  ((S ⊙ composition R S n) ⊙ S) p  ↔⟨ inverse $ ⊙-assoc S S _ ⟩
  (S ⊙ (composition R S n ⊙ S)) p  ↝⟨ ⊙-cong (λ p → S p □) (composition-⊙-comm hyp n) _ ⟩□
  (S ⊙ (S ⊙ composition R S n)) p  □

composition⊙composition :
  ∀ {k a} {A : Type a} {R S : Rel₂ a A} m n₁ {n₂} →
  (∀ p → (R ⊙ composition R S n₁) p ↝[ k ] composition R S n₂ p) →
  ∀ p → (composition R S m ⊙ composition R S n₁) p ↝[ k ]
        composition R S (m + n₂) p
composition⊙composition {R = R} {S} = λ where
  zero n₁ {n₂} hyp p →
    (R ⊙ composition R S n₁) p  ↝⟨ hyp _ ⟩
    composition R S n₂ p        □
  (suc m) n₁ {n₂} hyp p →
    ((S ⊙ composition R S m) ⊙ composition R S n₁) p  ↔⟨ inverse $ ⊙-assoc S (composition R S n₁) _ ⟩
    (S ⊙ (composition R S m ⊙ composition R S n₁)) p  ↝⟨ ⊙-cong (λ p → S p □) (composition⊙composition m n₁ hyp) _ ⟩□
    (S ⊙ composition R S (m + n₂)) p            □

-- The transitive closure is transitive.

⁺-trans : ∀ {a} {A : Type a} {R : Rel₂ a A} {x y z} →
          (R ⁺) (x , y) → (R ⁺) (y , z) → (R ⁺) (x , z)
⁺-trans (m , xR¹⁺ᵐy) (n , yR¹⁺ⁿz) =
    m + suc n
  , composition⊙composition m n (λ _ → id) _ (_ , xR¹⁺ᵐy , yR¹⁺ⁿz)

-- The reflexive transitive closure is transitive.

*-trans : ∀ {a} {A : Type a} {R : Rel₂ a A} {x y z} →
          (R *) (x , y) → (R *) (y , z) → (R *) (x , z)
*-trans {R = R} (m , xRᵐy) (n , yRⁿz) =
  m + n , composition⊙composition m n lemma _ (_ , xRᵐy , yRⁿz)
  where
  lemma : ∀ p → (uncurry _≡_ ⊙ (R ^^ n)) p → (R ^^ n) p
  lemma _ (_ , refl , r) = r

-- Lemmas relating different forms of composition and swap.

⊙-swap :
  ∀ {k a r s} {A : Type a} {R : Rel₂ r A} {S : Rel₂ s A} →
  (∀ p → R p ↝[ k ] R (swap p)) →
  (∀ p → S p ↝[ k ] S (swap p)) →
  ∀ p → (R ⊙ S) p ↝[ k ] (S ⊙ R) (swap p)
⊙-swap {R = R} {S} R↝ S↝ (x , z) =
  (∃ λ y → R (x , y) × S (y , z))  ↝⟨ ∃-cong (λ _ → R↝ _ ×-cong S↝ _) ⟩
  (∃ λ y → R (y , x) × S (z , y))  ↔⟨ ∃-cong (λ _ → ×-comm) ⟩□
  (∃ λ y → S (z , y) × R (y , x))  □

composition-swap :
  ∀ {k a} {A : Type a} {R S : Rel₂ a A} →
  (∀ p → R p ↝[ k ] R (swap p)) →
  (∀ p → S p ↝[ k ] S (swap p)) →
  (∀ p → (R ⊙ S) p ↝[ k ] (S ⊙ R) p) →
  ∀ n p → composition R S n p ↝[ k ] composition R S n (swap p)
composition-swap {R = R} {S} R↝ S↝ hyp = λ where
  zero    p → R p         ↝⟨ R↝ _ ⟩□
              R (swap p)  □
  (suc n) p → (S ⊙ composition R S n) p         ↝⟨ ⊙-swap S↝ (composition-swap R↝ S↝ hyp n) _ ⟩
              (composition R S n ⊙ S) (swap p)  ↝⟨ composition-⊙-comm hyp n _ ⟩□
              (S ⊙ composition R S n) (swap p)  □

^^[1+]-swap :
  ∀ {k a} {A : Type a} {R : Rel₂ a A} →
  (∀ p → R p ↝[ k ] R (swap p)) →
  ∀ n p → (R ^^[1+ n ]) p ↝[ k ] (R ^^[1+ n ]) (swap p)
^^[1+]-swap R↝ = composition-swap R↝ R↝ (λ _ → _ □)

^^-swap :
  ∀ {k a} {A : Type a} {R : Rel₂ a A} →
  (∀ p → R p ↝[ k ] R (swap p)) →
  ∀ n p → (R ^^ n) p ↝[ k ] (R ^^ n) (swap p)
^^-swap {R = R} R↝ = composition-swap lemma₁ R↝ lemma₂
  where
  lemma₁ = λ { (x , y) →
    x ≡ y  ↔⟨ Groupoid.⁻¹-bijection (EG.groupoid _) ⟩□
    y ≡ x  □ }

  lemma₂ = λ { (x , z) →
    (∃ λ y → x ≡ y × R (y , z))  ↔⟨ ∃-cong (λ _ → ×-comm) ⟩
    (∃ λ y → R (y , z) × x ≡ y)  ↝⟨ ∃-cong (λ _ → ∃-cong λ _ → lemma₁ _) ⟩
    (∃ λ y → R (y , z) × y ≡ x)  ↔⟨ inverse $ ∃-intro _ _ ⟩
    R (x , z)                    ↔⟨ ∃-intro _ _ ⟩□
    (∃ λ y → R (x , y) × y ≡ z)  □}

⁺-swap :
  ∀ {k a} {A : Type a} {R : Rel₂ a A} →
  (∀ p → R p ↝[ k ] R (swap p)) →
  ∀ p → (R ⁺) p ↝[ k ] (R ⁺) (swap p)
⁺-swap {R = R} R↝ p =
  (R ⁺) p                           ↔⟨⟩
  (∃ λ n → (R ^^[1+ n ]) p)         ↝⟨ ∃-cong (λ n → ^^[1+]-swap R↝ n _) ⟩
  (∃ λ n → (R ^^[1+ n ]) (swap p))  ↔⟨⟩
  (R ⁺) (swap p)                    □

*-swap :
  ∀ {k a} {A : Type a} {R : Rel₂ a A} →
  (∀ p → R p ↝[ k ] R (swap p)) →
  ∀ p → (R *) p ↝[ k ] (R *) (swap p)
*-swap {R = R} R↝ p =
  (R *) p                      ↔⟨⟩
  (∃ λ n → (R ^^ n) p)         ↝⟨ ∃-cong (λ n → ^^-swap R↝ n _) ⟩
  (∃ λ n → (R ^^ n) (swap p))  ↔⟨⟩
  (R *) (swap p)               □

-- ⋃ constructs least upper bounds.

⊆-⋃ : ∀ {a b ℓ} {A : Type a} {B : Type b}
      (F : A → Trans (a ⊔ ℓ) B) a →
      ∀ R → F a R ⊆ ⋃ ℓ F R
⊆-⋃ {ℓ = ℓ} F a R =
  F a R                    ⊆⟨ a ,_ ⟩
  (λ x → ∃ λ a → F a R x)  ⊆⟨ id ⟩∎
  ⋃ ℓ F R                  ∎

⋃-⊆ : ∀ {a b ℓ} {A : Type a} {B : Type b}
      (F : A → Trans (a ⊔ ℓ) B) (G : Trans (a ⊔ ℓ) B) →
      (∀ {a} R → F a R ⊆ G R) →
      ∀ R → ⋃ ℓ F R ⊆ G R
⋃-⊆ {ℓ = ℓ} F G hyp R =
  ⋃ ℓ F R                  ⊆⟨⟩
  (λ x → ∃ λ a → F a R x)  ⊆⟨ hyp _ ∘ proj₂ ⟩∎
  G R                      ∎
