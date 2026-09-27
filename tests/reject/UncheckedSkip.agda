{-# OPTIONS --safe --without-K #-}
-- Rejection control: a skip whose check was not accepted.
--
-- The four-taxon scan below is unscannable past its cursor.  With r = 4
-- (coefficient 2), row sum t(i) = 1, running maximum t(max) = 20, cursor
-- distance 5, and incumbent q(min) = 0,
--
--     qBound = (r - 2)*5 - 1 - 20 = 10 - 21 = -11 < 0 = q(min)
--
-- so the bound *can* be improved further down the row and an exact
-- comparison answers `false`.  Recording that run as evidence would be
-- unsound: it asserts a stop condition the numbers do not meet.  The
-- `refl` below is therefore rejected -- the check is the gate, and the
-- Q-criterion bound lemma consumes only accepted checks.
module UncheckedSkip where

open import Agda.Builtin.Equality using (refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.Sigma using (_,_)
open import EpistemicTypes.EchoBridge using (≤ℕ-plus)
open import EpistemicTypes.Applications.IntegerModel using (mk; ≤ℕ-refl; ℤ-group)
open import EpistemicTypes.Applications.RapidNJExamples using (ℤ-checkable; ≤ℤ-5-7)
import EpistemicTypes.Applications.RapidNJSkip
import EpistemicTypes.Applications.SortedRow
import EpistemicTypes.Applications.QCriterion

module Rapid = EpistemicTypes.Applications.RapidNJSkip.Skip ℤ-group
module Row = EpistemicTypes.Applications.SortedRow.Row ℤ-group
module Cr =
  EpistemicTypes.Applications.QCriterion.Criterion ℤ-group

open Rapid
open Row
open Cr

state : ScanState
state = scanning (numbers 2 (mk 1) (mk 20) (mk 0))
                 (entry 2 (mk 5) (mk 1))
                 (entry 3 (mk 7) (mk 2) ∷ [])

forged : SkipEvidence ℤ-checkable state
forged = allCons ≤ℤ-5-7 allNil
       , allCons (≤ℕ-plus 2 18) allNil
       , refl
