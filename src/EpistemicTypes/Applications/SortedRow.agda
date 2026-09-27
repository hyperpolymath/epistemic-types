{-# OPTIONS --safe --without-K #-}

-- Applications / SortedRow
--
-- The scan state of a RapidNJ row.  RapidNJ keeps, beside the distance
-- matrix D, a matrix S whose rows are sorted by increasing distance, and an
-- index map I.  For each cluster i it walks S(i) upwards from small to
-- large d(i,j), keeping the smallest q-value seen so far, and stops as soon
-- as the row lower bound cannot improve it.  The entries it never looks at
-- are what this module calls the skipped suffix: in the (index, distance)
-- plane they are the quadrant `{ (i,j) : d(i,j) ≥ d(i,next) }`.
--
-- The two facts the bound argument needs about that quadrant are:
--
--   * every skipped distance is at least the distance at the stop cursor
--     (`AllDistAtLeast`, the sorted-row invariant), and
--   * every skipped row sum is at most the running maximum
--     (`AllRowSumAtMost`, the running-maximum invariant).
--
-- Both are carried as *proof objects*, not consumed silently: a certificate
-- that cannot supply them is not a certificate.  The implementation
-- maintains them when it inserts the new cluster row after a join.

module EpistemicTypes.Applications.SortedRow where

open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)

open import EpistemicTypes.Applications.OrderedGroup
open import EpistemicTypes.Applications.IntegerModel using (_⊎_; inj₁; inj₂)

-- The row layer, parameterised by the exact arithmetic it reasons about.
module Row (G : OrderedGroup) where
  open OrderedGroup G
  open Laws G

  -- A row entry: the column index j, the distance d(i,j) as seen from the
  -- row's cluster i, and the row sum t(j) of the column.
  record Entry : Set where
    constructor entry
    field
      index  : Nat
      dist   : Carrier
      rowSum : Carrier

  -- P holds of every entry of the list.
  data All (P : Entry -> Set) : List Entry -> Set where
    allNil  : All P []
    allCons : {e : Entry} {es : List Entry} -> P e -> All P es -> All P (e ∷ es)

  -- Membership.
  data _∈E_ (e : Entry) : List Entry -> Set where
    here  : {es : List Entry} -> e ∈E (e ∷ es)
    there : {e' : Entry} {es : List Entry} -> e ∈E es -> e ∈E (e' ∷ es)

  ∈-All : (P : Entry -> Set) {es : List Entry} ->
    All P es -> (x : Entry) -> x ∈E es -> P x
  ∈-All P (allCons p _) x here = p
  ∈-All P (allCons p ps) x (there i) = ∈-All P ps x i

  -- The sorted-row invariant, relative to the stop cursor: the cursor's
  -- distance is a lower bound for the whole skipped suffix.
  AllDistAtLeast : (d : Carrier) -> List Entry -> Set
  AllDistAtLeast d = All (λ e -> d ≤ Entry.dist e)

  -- The running-maximum invariant: no skipped row sum exceeds t(max).
  AllRowSumAtMost : (b : Carrier) -> List Entry -> Set
  AllRowSumAtMost b = All (λ e -> Entry.rowSum e ≤ b)

  -- Concatenation of rows, and the decomposition of membership along it.
  -- A whole row is the examined prefix followed by the skipped suffix.
  _++_ : List Entry -> List Entry -> List Entry
  [] ++ ys = ys
  (x ∷ xs) ++ ys = x ∷ (xs ++ ys)

  ∈-append : {e : Entry} {xs ys : List Entry} ->
    e ∈E (xs ++ ys) -> e ∈E xs ⊎ e ∈E ys
  ∈-append {e} {xs = []} {ys} i = inj₂ i
  ∈-append {e} {xs = x ∷ xs} {ys} here = inj₁ here
  ∈-append {e} {xs = x ∷ xs} {ys} (there i) with ∈-append {e} {xs = xs} {ys} i
  ... | inj₁ p = inj₁ (there p)
  ... | inj₂ q = inj₂ q
