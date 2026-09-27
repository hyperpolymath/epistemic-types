{-# OPTIONS --safe --without-K #-}

-- Applications / OrderedGroup
--
-- The exact-arithmetic contract consumed by the RapidNJ Q-criterion proof.
--
-- RapidNJ (Simonsen, Mailund & Pedersen 2008) prunes its search for the
-- minimum q-value with the row lower bound
--
--     q_bound = (r - 2) * d(i, next) - t(i) - t(max)
--
-- where r is the number of remaining clusters, t(i) is the i-th row sum of
-- the distance matrix, t(max) is the largest row sum still under
-- consideration, and d(i, next) is the smallest distance not yet examined
-- in the sorted row S(i).  The bound is only a bound if the arithmetic is
-- exact: every inequality manipulation used below must be order-monotone.
--
-- This record states the *whole* assumption budget of that argument.  It is
-- deliberately weaker than "field" or even "ring": the Q-criterion proof
-- never multiplies two carrier elements, never divides, and never needs
-- associativity, commutativity or distributivity, because each step in the
-- proof adds the *syntactically identical* term to both sides.  What it does
-- need is that `_+_` and `neg` are monotone for `_≤_`, and that `_≤_` is
-- transitive.  Multiplication by the coefficient (r - 2) is definable as
-- repeated addition (`scale` below), so non-negativity of that coefficient
-- is a *typing* fact (it is a Nat), not an extra law.
--
-- Consequences that matter for the applications section:
--
--  * Any model of these four laws certifies the bound, so the bound does not
--    depend on the *representation* of rationals, only on exactness.
--  * A Float64 implementation does not satisfy `≤-⊕`: rounding is not
--    monotone for every pair of operands, so `x ≤ y` can hold while
--    `x + z > y + z` holds under rounding.  That is the seam documented in
--    link:docs/applications/rapidnj-q-criterion.adoc[], and the reason the
--    reflection lemma in `RapidNJSkip` is the single non-negotiable
--    obligation of an executable implementation.
--
-- `zeroC` is present so that a zero-length scaling exists.  No identity law
-- for it is assumed, and none is consumed by any proof in this development.

module EpistemicTypes.Applications.OrderedGroup where

open import Agda.Builtin.Nat using (Nat; zero; suc)

record OrderedGroup : Set₁ where
  infixl 6 _⊕_
  infix 4 _≤_
  field
    Carrier : Set

    _⊕_ : Carrier -> Carrier -> Carrier
    neg : Carrier -> Carrier
    zeroC : Carrier

    _≤_ : Carrier -> Carrier -> Set

    -- Reflexivity and transitivity of the order.
    ≤-refl  : {x : Carrier} -> x ≤ x
    ≤-trans : {x y z : Carrier} -> x ≤ y -> y ≤ z -> x ≤ z

    -- Addition is monotone in both arguments simultaneously.  The two
    -- one-sided rules used by the proof are derived below, so this is the
    -- only addition law assumed.
    ≤-⊕ : {x y u v : Carrier} -> x ≤ y -> u ≤ v -> x ⊕ u ≤ y ⊕ v

    -- Negation is antitone.  This is the only rule that lets the proof
    -- replace an upper bound (t(max)) by an entry's own row sum (t(j)).
    ≤-neg : {x y : Carrier} -> x ≤ y -> neg y ≤ neg x

-- Derived rules and the coefficient scaling.  Nothing here is assumed.
module Laws (G : OrderedGroup) where
  open OrderedGroup G

  -- Addition monotone on the right, used to move a fixed summand across.
  ≤-⊕-right : {x y : Carrier} (z : Carrier) -> x ≤ y -> x ⊕ z ≤ y ⊕ z
  ≤-⊕-right z p = ≤-⊕ p ≤-refl

  -- Addition monotone on the left, the mirror rule.
  ≤-⊕-left : (z : Carrier) {x y : Carrier} -> x ≤ y -> z ⊕ x ≤ z ⊕ y
  ≤-⊕-left z p = ≤-⊕ ≤-refl p

  -- x - y, i.e. x + (-y).  Subtraction is notation here, not structure:
  -- no inverse law is assumed or needed.
  _⊖_ : Carrier -> Carrier -> Carrier
  x ⊖ y = x ⊕ neg y

  ≤-⊖-right : {x y : Carrier} (z : Carrier) -> x ≤ y -> x ⊖ z ≤ y ⊖ z
  ≤-⊖-right z p = ≤-⊕-right (neg z) p

  -- The "slide an upper bound past a subtraction" rule.
  ≤-⊖-anti : {x y z : Carrier} -> x ≤ y -> z ⊖ y ≤ z ⊖ x
  ≤-⊖-anti {z = z} p = ≤-⊕-left z (≤-neg p)

  -- Repeated addition: the coefficient (r - 2) is applied as a Nat, so it
  -- cannot be negative and needs no sign side condition.
  scale : Nat -> Carrier -> Carrier
  scale zero x = zeroC
  scale (suc k) x = scale k x ⊕ x

  -- Non-negative scaling is monotone, by induction on the coefficient.
  -- This is the only place where the coefficient enters the bound proof.
  scale-mono : {x y : Carrier} (k : Nat) -> x ≤ y -> scale k x ≤ scale k y
  scale-mono zero p = ≤-refl
  scale-mono (suc k) p = ≤-⊕ (scale-mono k p) p

  -- Combining a certificate with a slack element.  A certificate that only
  -- establishes `q_bound ⊕ ε ≤ q₀` proves a strictly weaker claim than one
  -- establishing `q_bound ≤ q₀`; see `RapidNJSkip.noBetter-weaken`, which
  -- makes that weakness explicit instead of hiding it.
  ≤-with-slack : {a b c : Carrier} -> a ≤ b -> b ≤ c -> a ≤ c
  ≤-with-slack = ≤-trans
