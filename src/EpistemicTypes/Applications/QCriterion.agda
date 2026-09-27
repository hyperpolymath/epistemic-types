{-# OPTIONS --safe --without-K #-}

-- Applications / QCriterion
--
-- The mathematical core of the RapidNJ quadrant skip, stated over an
-- arbitrary exact `OrderedGroup`:
--
--   qBound(k, t(i), t(max), d(i,next))
--             = (r - 2) * d(i,next) - t(i) - t(max)      (k = r - 2)
--   Q(k, t(i), t(j), d(i,j))
--             = (r - 2) * d(i,j)    - t(i) - t(j)
--
-- and the row lemma: if the stop cursor's distance is no greater than any
-- skipped distance, and t(max) bounds every skipped row sum, then the bound
-- at the cursor is below every skipped q-value.  That is precisely the
-- statement "the unvisited part of the row cannot improve q(min)".
--
-- The bound theorem (`qBound-≤-Q`) is the load-bearing part.  It uses only
-- monotonicity of addition, antitonicity of negation, and transitivity of
-- the order -- no associativity, commutativity, or distributivity of the
-- carrier.  This is why the applications section can work over the
-- difference-pair model of the integers without first developing ℚ: see the
-- header of `EpistemicTypes.Applications.IntegerModel`.

module EpistemicTypes.Applications.QCriterion where

open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat)

open import EpistemicTypes.Applications.OrderedGroup
open import EpistemicTypes.Applications.IntegerModel using (_⊎_; inj₁; inj₂)
import EpistemicTypes.Applications.SortedRow as SortedRow

-- The criterion, parameterised by the exact arithmetic it reasons about.
module Criterion (G : OrderedGroup) where
  open OrderedGroup G
  open Laws G
  open SortedRow.Row G

  -- The numbers a scan step carries, exactly as a log line would record
  -- them.
  record Numbers : Set where
    constructor numbers
    field
      coefficient : Nat      -- r - 2, as a natural number
      row-sum-i   : Carrier  -- t(i)
      row-sum-max : Carrier  -- t(max), the running maximum
      incumbent   : Carrier  -- the smallest q-value seen so far

  -- The Neighbour-Joining optimality criterion.
  Q : Nat -> Carrier -> Carrier -> Carrier -> Carrier
  Q k ti tj d = ((scale k d) ⊕ neg ti) ⊕ neg tj

  -- The RapidNJ row lower bound at the stop cursor.
  qBound : Nat -> Carrier -> Carrier -> Carrier -> Carrier
  qBound k ti tmax dnext = ((scale k dnext) ⊕ neg ti) ⊕ neg tmax

  -- The bound really is below every q-value of a skipped entry.  Note the
  -- shape of the proof: add the same term on the right (monotonicity),
  -- replace t(j) by the larger t(max) (antitonicity under negation), and
  -- chain.  No ring identity is used, so no ring axiom is needed.
  qBound-≤-Q : (k : Nat) {ti tmax tj dnext d : Carrier} ->
    dnext ≤ d -> tj ≤ tmax -> qBound k ti tmax dnext ≤ Q k ti tj d
  qBound-≤-Q k {ti} {tmax} {tj} {dnext} {d} dnext≤d tj≤tmax =
    ≤-trans inside-≤bound (≤-⊕ ≤-refl (≤-neg tj≤tmax))
    where
    -- Compare the two scaled distances with the same tails, then hang
    -- t(max) and t(j) off the right in turn.
    first : (scale k dnext) ⊕ neg ti ≤ (scale k d) ⊕ neg ti
    first = ≤-⊕ (scale-mono k dnext≤d) ≤-refl

    inside-≤bound : ((scale k dnext) ⊕ neg ti) ⊕ neg tmax ≤
                    ((scale k d) ⊕ neg ti) ⊕ neg tmax
    inside-≤bound = ≤-⊕ first ≤-refl

  -- The claim a skip certifies: nothing in the skipped suffix beats the
  -- incumbent.
  SkipClaim : (k : Nat) (ti q₀ : Carrier) -> List Entry -> Set
  SkipClaim k ti q₀ es =
    (e : Entry) -> e ∈E es -> q₀ ≤ Q k ti (Entry.rowSum e) (Entry.dist e)

  -- Row-level soundness: invariants plus an accepted check entail the
  -- claim.
  qBound-≤-suffix :
    {k : Nat} {ti tmax q₀ : Carrier} {cursor : Entry} {suffix : List Entry} ->
    AllDistAtLeast (Entry.dist cursor) suffix ->
    AllRowSumAtMost tmax suffix ->
    q₀ ≤ qBound k ti tmax (Entry.dist cursor) ->
    SkipClaim k ti q₀ suffix
  qBound-≤-suffix {k = k} {ti = ti} {tmax = tmax} {q₀ = q₀} {cursor = cursor}
                  ordered maximal accepted e i =
    ≤-trans accepted
      (qBound-≤-Q k
        (∈-All (λ x -> Entry.dist cursor ≤ Entry.dist x) ordered e i)
        (∈-All (λ x -> Entry.rowSum x ≤ tmax) maximal e i))

  -- Lowering the incumbent weakens the claim.  This is the lemma that makes
  -- an explicit slack visible instead of hiding it.
  noBetter-weaken : {k : Nat} {ti q1 q₀ : Carrier} {es : List Entry} ->
    q1 ≤ q₀ -> SkipClaim k ti q₀ es -> SkipClaim k ti q1 es
  noBetter-weaken {k} {ti} q1≤q₀ claim e i = ≤-trans q1≤q₀ (claim e i)

  -- Examined prefix plus certified suffix covers the whole row.  A quadrant
  -- skip composes back into a whole-row guarantee through this lemma.
  noBetter-append :
    {k : Nat} {ti q₀ : Carrier} {pre suf : List Entry} ->
    ((e : Entry) -> e ∈E pre -> q₀ ≤ Q k ti (Entry.rowSum e) (Entry.dist e)) ->
    SkipClaim k ti q₀ suf ->
    (e : Entry) -> e ∈E (pre ++ suf) -> q₀ ≤ Q k ti (Entry.rowSum e) (Entry.dist e)
  noBetter-append {pre = pre} {suf = suf} scanned skipped e i
    with ∈-append {e = e} {xs = pre} {ys = suf} i
  ... | inj₁ p = scanned e p
  ... | inj₂ q = skipped e q
