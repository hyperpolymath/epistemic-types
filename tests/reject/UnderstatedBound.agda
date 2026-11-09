{-# OPTIONS --safe --without-K --cubical-compatible --exact-split --no-sized-types --no-guardedness #-}
module UnderstatedBound where
-- Audit 2026-11-09: this retypes `boundedTrue` (budget `finite 1`) at budget
-- `finite 0`, so it fails on the budget index whatever the cost measure is.
-- The bound check itself is shown by the positive `noUnderstatedBound`.
open import Agda.Builtin.Bool
open import Agda.Builtin.Nat
open import EpistemicTypes.EchoBridge
import EpistemicTypes.ContinuityExamples as Examples
open Examples.Residues using (identityRetention; constantCost; boundedTrue)
forged : BoundedEcho identityRetention constantCost (finite zero) true
forged = boundedTrue
