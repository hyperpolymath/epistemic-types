{-# OPTIONS --safe --without-K #-}

-- Applications / IntegerModel
--
-- A concrete model of `OrderedGroup`: the integers, represented as
-- difference pairs of naturals (mkℤ a b read as a - b).  The point of this
-- module is non-vacuity.  A specification that assumed an ordered group
-- without exhibiting one would prove nothing about the RapidNJ bound, so
-- the four laws of `OrderedGroup` are proved here for an exact model.
--
-- Why integers rather than a developed ℚ here.  The whole hypothesis budget
-- the Q-criterion proof consumes is order-compatibility of `+` and `neg`
-- (see `EpistemicTypes.Applications.OrderedGroup`); it never divides and
-- never multiplies two carrier elements.  Clearing denominators in a
-- rational distance matrix is therefore invisible to the bound argument:
-- for a common positive denominator D, comparing q-values of a ℚ matrix is
-- the same comparison as for its integer rescaling by D, and scaling by the
-- coefficient (r - 2) commutes with that rescaling.  The worked matrices in
-- `RapidNJExamples` are integer matrices for exactly this reason.
--
-- The ℚ instance itself (numerator/denominator pairs with cross-multiplied
-- order) is deliberately NOT claimed here: it needs multiplication
-- monotonicity, which the difference-pair development below does not
-- provide.  It is listed as an explicit obligation in
-- link:docs/applications/rapidnj-q-criterion.adoc[], not as a theorem.
--
-- The order on naturals is reused from `EpistemicTypes.EchoBridge`, so the
-- resource grades there and the arithmetic order here are one relation.

module EpistemicTypes.Applications.IntegerModel where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

-- The equality helpers the builtin module does not export.  They are
-- defined here (rather than imported) because this development is built
-- with `--no-libraries`; the definitions are the standard ones.
sym : {A : Set} {x y : A} -> x ≡ y -> y ≡ x
sym refl = refl

trans : {A : Set} {x y z : A} -> x ≡ y -> y ≡ z -> x ≡ z
trans refl q = q

cong : {A B : Set} (f : A -> B) {x y : A} -> x ≡ y -> f x ≡ f y
cong f refl = refl

-- A local disjoint sum: a witness, or a proof that there is none.
infixr 1 _⊎_
data _⊎_ (A B : Set) : Set where
  inj₁ : A -> A ⊎ B
  inj₂ : B -> A ⊎ B

open import EpistemicTypes.EchoBridge using
  (Impossible; _≤ℕ_; zero≤; suc≤; ≤ℕ-trans; ≤ℕ-plus)
open import EpistemicTypes.Applications.OrderedGroup

-- ── Naturals ────────────────────────────────────────────────────────────────

+0 : (m : Nat) -> m + zero ≡ m
+0 zero = refl
+0 (suc m) = cong suc (+0 m)

+suc : (m n : Nat) -> m + suc n ≡ suc (m + n)
+suc zero n = refl
+suc (suc m) n = cong suc (+suc m n)

+-assoc : (a b c : Nat) -> (a + b) + c ≡ a + (b + c)
+-assoc zero b c = refl
+-assoc (suc a) b c = cong suc (+-assoc a b c)

+-comm : (a b : Nat) -> a + b ≡ b + a
+-comm zero b = sym (+0 b)
+-comm (suc a) b = trans (cong suc (+-comm a b)) (sym (+suc b a))

≤ℕ-refl : (m : Nat) -> m ≤ℕ m
≤ℕ-refl zero = zero≤
≤ℕ-refl (suc m) = suc≤ (≤ℕ-refl m)

≤ℕ-pred : {m n : Nat} -> suc m ≤ℕ suc n -> m ≤ℕ n
≤ℕ-pred (suc≤ p) = p

-- Transport an inequality along equalities of its two sides: the statement
-- is unchanged by regrouping its operands.
≤ℕ-cong : {m n m' n' : Nat} -> m ≡ m' -> n ≡ n' -> m ≤ℕ n -> m' ≤ℕ n'
≤ℕ-cong refl refl p = p

-- Move an inequality right by a common summand.
≤ℕ-shift : {m n : Nat} (k : Nat) -> m ≤ℕ n -> m + k ≤ℕ n + k
≤ℕ-shift {m = zero} {n = n} k zero≤ = ≤ℕ-cong refl (+-comm k n) (≤ℕ-plus k n)
≤ℕ-shift {m = suc m} {n = suc n} k (suc≤ p) = suc≤ (≤ℕ-shift k p)

-- Move an inequality left by a common summand.
≤ℕ-shift-left : (k : Nat) -> {m n : Nat} -> m ≤ℕ n -> k + m ≤ℕ k + n
≤ℕ-shift-left zero p = p
≤ℕ-shift-left (suc k) p = suc≤ (≤ℕ-shift-left k p)

-- Inequality is compatible with addition in both arguments.
≤ℕ-add : {a b c d : Nat} -> a ≤ℕ b -> c ≤ℕ d -> a + c ≤ℕ b + d
≤ℕ-add {a} {b} {c} p q = ≤ℕ-trans (≤ℕ-shift c p) (≤ℕ-shift-left b q)

-- A common right summand can be cancelled.  This is the rule that turns
-- "add the same term to both sides" back into the original inequality.
≤ℕ-cancel : {m n : Nat} (k : Nat) -> m + k ≤ℕ n + k -> m ≤ℕ n
≤ℕ-cancel zero p = ≤ℕ-cong (+0 _) (+0 _) p
≤ℕ-cancel {m} {n} (suc k) p =
  ≤ℕ-cancel k (≤ℕ-pred (≤ℕ-cong (+suc m k) (+suc n k) p))

-- Two four-term regroupings, proved once and reused by the group laws.
-- interleave-AD pairs the outer terms; interleave-AC pairs adjacent terms.
interleave-AC : (a b c d : Nat) -> (a + b) + (c + d) ≡ (a + c) + (b + d)
interleave-AC a b c d =
  trans (+-assoc a b (c + d))
    (trans (cong (a +_) (sym (+-assoc b c d)))
      (trans (cong (a +_) (cong (_+ d) (+-comm b c)))
        (trans (cong (a +_) (+-assoc c b d))
          (sym (+-assoc a c (b + d))))))

-- The outer pairing follows from the adjacent one by commuting the middle
-- pair.
interleave-AD : (a b c d : Nat) -> (a + b) + (c + d) ≡ (a + d) + (c + b)
interleave-AD a b c d =
  trans (interleave-AC a b c d)
    (trans (cong ((a + c) +_) (+-comm b d))
      (interleave-AC a c d b))

-- ── Integers as difference pairs ────────────────────────────────────────────

record ℤ : Set where
  constructor mkℤ
  field
    plus  : Nat
    minus : Nat

-- Field projections, unqualified, so the arithmetic below reads as
-- arithmetic.
open ℤ

_+ℤ_ : ℤ -> ℤ -> ℤ
mkℤ a b +ℤ mkℤ c d = mkℤ (a + c) (b + d)

negℤ : ℤ -> ℤ
negℤ (mkℤ a b) = mkℤ b a

zeroℤ : ℤ
zeroℤ = mkℤ zero zero

-- a ⊖ b ≤ c ⊖ d  iff  a + d ≤ c + b, i.e. a - b ≤ c - d.
_≤ℤ_ : ℤ -> ℤ -> Set
x ≤ℤ y = (ℤ.plus x + ℤ.minus y) ≤ℕ (ℤ.plus y + ℤ.minus x)

-- Congruence for addition, and the two projection laws that let a proof
-- rewrite `plus (x +ℤ y)` into its components.
+-cong : {a a' b b' : Nat} -> a ≡ a' -> b ≡ b' -> a + b ≡ a' + b'
+-cong refl refl = refl

plus-+ℤ : (x y : ℤ) -> plus (x +ℤ y) ≡ plus x + plus y
plus-+ℤ (mkℤ a b) (mkℤ c d) = refl

minus-+ℤ : (x y : ℤ) -> minus (x +ℤ y) ≡ minus x + minus y
minus-+ℤ (mkℤ a b) (mkℤ c d) = refl

plus-negℤ : (x : ℤ) -> plus (negℤ x) ≡ minus x
plus-negℤ (mkℤ a b) = refl

minus-negℤ : (x : ℤ) -> minus (negℤ x) ≡ plus x
minus-negℤ (mkℤ a b) = refl

≤ℤ-refl : {x : ℤ} -> x ≤ℤ x
≤ℤ-refl {x} = ≤ℕ-refl (plus x + minus x)

≤ℤ-trans : {x y z : ℤ} -> x ≤ℤ y -> y ≤ℤ z -> x ≤ℤ z
≤ℤ-trans {x} {y} {z} p q =
  ≤ℕ-cancel (plus y + minus y)
    (≤ℕ-cong (interleave-AD (plus x) (minus y) (plus y) (minus z))
      (trans (interleave-AD (plus y) (minus x) (plus z) (minus y))
        (+-comm (plus y + minus y) (plus z + minus x)))
      (≤ℕ-add p q))

≤ℤ-⊕ : {x y u v : ℤ} -> x ≤ℤ y -> u ≤ℤ v -> (x +ℤ u) ≤ℤ (y +ℤ v)
≤ℤ-⊕ {x} {y} {u} {v} p q =
  ≤ℕ-cong (sym (+-cong (plus-+ℤ x u) (minus-+ℤ y v)))
          (sym (+-cong (plus-+ℤ y v) (minus-+ℤ x u)))
    (≤ℕ-cong (interleave-AC (plus x) (minus y) (plus u) (minus v))
      (interleave-AC (plus y) (minus x) (plus v) (minus u))
      (≤ℕ-add p q))

≤ℤ-neg : {x y : ℤ} -> x ≤ℤ y -> negℤ y ≤ℤ negℤ x
≤ℤ-neg {x} {y} p =
  ≤ℕ-cong
    (trans (+-comm (plus x) (minus y))
           (sym (+-cong (plus-negℤ y) (minus-negℤ x))))
    (trans (+-comm (plus y) (minus x))
           (sym (+-cong (plus-negℤ x) (minus-negℤ y))))
    p

-- The exact model.  This is the witness that `OrderedGroup` is inhabited,
-- and therefore that the Q-criterion theorem below is not vacuous.
ℤ-group : OrderedGroup
ℤ-group = record
  { Carrier = ℤ
  ; _⊕_ = _+ℤ_
  ; neg = negℤ
  ; zeroC = zeroℤ
  ; _≤_ = _≤ℤ_
  ; ≤-refl = λ {x} -> ≤ℤ-refl {x}
  ; ≤-trans = λ {x} {y} {z} -> ≤ℤ-trans {x} {y} {z}
  ; ≤-⊕ = λ {x} {y} {u} {v} -> ≤ℤ-⊕ {x} {y} {u} {v}
  ; ≤-neg = λ {x} {y} -> ≤ℤ-neg {x} {y}
  }

-- ── Numerals and decidable comparison ───────────────────────────────────────

-- Non-negative literals.
mk : Nat -> ℤ
mk n = mkℤ n zero

-- Negative literals: `negM n` is -n.
negM : Nat -> ℤ
negM n = mkℤ zero n

mk-+ℤ : (m n : Nat) -> mk m +ℤ mk n ≡ mk (m + n)
mk-+ℤ m n = refl

mk-negℤ : (n : Nat) -> negℤ (mk n) ≡ negM n
mk-negℤ n = refl

-- The comparison an implementation actually performs.  A total decision
-- procedure is *not* part of `OrderedGroup` (the bound theorem does not
-- need one); it is needed only to turn the bound into a checkable
-- certificate, and its reflection lemma is where exactness is consumed.
dec-≤ℕ : (m n : Nat) -> m ≤ℕ n ⊎ (m ≤ℕ n -> Impossible)
dec-≤ℕ zero n = inj₁ zero≤
dec-≤ℕ (suc m) zero = inj₂ (λ ())
dec-≤ℕ (suc m) (suc n) with dec-≤ℕ m n
... | inj₁ p = inj₁ (suc≤ p)
... | inj₂ f = inj₂ (λ { (suc≤ q) -> f q })

dec-≤ℤ : (x y : ℤ) -> x ≤ℤ y ⊎ (x ≤ℤ y -> Impossible)
dec-≤ℤ x y = dec-≤ℕ (plus x + minus y) (plus y + minus x)
