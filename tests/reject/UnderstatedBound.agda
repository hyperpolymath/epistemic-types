{-# OPTIONS --safe --without-K --cubical-compatible --exact-split --no-sized-types --no-guardedness #-}
module UnderstatedBound where
-- Audit 2026-11-09: this retypes `boundedTrue` (budget `finite 1`) at budget
-- `finite 0`, so it fails on the budget index whatever the cost measure is.
-- The bound check itself is shown by the positive `noUnderstatedBound`.
open import Agda.Builtin.Bool
open import Agda.Builtin.Nat
open import Agda.Builtin.Bool
open import EpistemicTypes.EchoBridge
import EpistemicTypes.ContinuityExamples as Examples
open Examples.Residues using (identityRetention; constantCost; identityTrue)

-- A bounded echo must prove its cost is within the budget.  The residue
-- costs `finite 1`; the forgery claims budget `finite 0` and supplies the
-- proof that worked for budget `finite 1`.  It fails at the `within`
-- obligation, `1 ≤ 0`, not at an index.  (Rewritten 2026-11-09; the
-- earlier fixture retyped a finished value and failed on the budget
-- index whatever the cost measure was.)

-- EXPECTED-REJECTION
forged : BoundedEcho identityRetention constantCost (finite zero) true
forged = bounded identityTrue (finite≤ (suc≤ zero≤))
