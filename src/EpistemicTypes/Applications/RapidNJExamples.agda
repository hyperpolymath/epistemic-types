{-# OPTIONS --safe --without-K #-}

-- Applications / RapidNJExamples
--
-- The integer model of the applications layer, made concrete:
--
--   * a `Checkable` instance for ℤ, built from the decidable order
--     `IntegerModel.dec-≤ℤ`, so the skip pipeline can actually be run;
--   * the refutation that shows why an unsound comparison cannot be
--     installed (the rounding failure mode);
--   * a worked four-taxon scan: numbers, stop cursor, sorted suffix, an
--     accepted check, and the claim that `skip-known` *computes* for it;
--   * the status mirror of the runtime vocabulary used by
--     `EpistemicTypes.jl` (`epi_status ∈ {Factive, Belief, Collapsed, SansFibre}`).
--
-- Nothing here is assumed: every fact is discharged by computation on
-- literals, which is what makes the integers a non-vacuous witness for the
-- abstract bound theorem.

module EpistemicTypes.Applications.RapidNJExamples where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.Sigma using (Σ; _,_)

open import EpistemicTypes.EchoBridge using (Impossible; _≤ℕ_; zero≤; suc≤; ≤ℕ-plus)
open import EpistemicTypes.Applications.OrderedGroup
open import EpistemicTypes.Applications.IntegerModel using
  (ℤ; mk; mkℤ; negM; zeroℤ; negℤ; _+ℤ_; _≤ℤ_; _⊎_; inj₁; inj₂;
   dec-≤ℤ; ≤ℕ-refl; ℤ-group)
open import EpistemicTypes.Applications.SortedRow
open import EpistemicTypes.Applications.QCriterion
open import EpistemicTypes.Applications.RapidNJSkip

module Rapid = Skip ℤ-group
module Rowℤ = EpistemicTypes.Applications.SortedRow.Row ℤ-group
module Crℤ =
  EpistemicTypes.Applications.QCriterion.Criterion ℤ-group

open Rapid
open Rowℤ
open Crℤ

-- ── the executable comparison ──────────────────────────────────────────────

-- The decision carried together with its witness.  Packing both in one
-- `Σ` is what lets the record below be defined without `inspect`: the
-- `false` branch simply has no witness to give.
decide-ℤ : (x y : ℤ) -> Σ Bool (λ b -> b ≡ true -> x ≤ℤ y)
decide-ℤ x y with dec-≤ℤ x y
... | inj₁ p = true , (λ _ -> p)
... | inj₂ f = false , (λ ())

ℤ-decide : (x y : ℤ) -> Bool
ℤ-decide x y = Σ.fst (decide-ℤ x y)

ℤ-decide-true : {x y : ℤ} -> ℤ-decide x y ≡ true -> x ≤ℤ y
ℤ-decide-true {x} {y} = Σ.snd (decide-ℤ x y)

-- The seam, discharged for the integer model.
ℤ-checkable : Checkable
ℤ-checkable = record
  { decide = ℤ-decide
  ; decide-true = λ {x} {y} -> ℤ-decide-true {x} {y}
  }

-- ── why an inexact comparison cannot be installed ──────────────────────────

-- `suc m ≤ℕ zero` has no inhabitant; the coverage checker sees this
-- without any arithmetic.
suc≰zero : (m : Nat) -> suc m ≤ℕ zero -> Impossible
suc≰zero m ()

-- 1 ≤ 0 is refutable in the integer model: the cross-multiplied form
-- normalises to `suc zero ≤ℕ zero`, so the argument is already an
-- impossible pattern.
not-le-ten : mk (suc zero) ≤ℤ mk zero -> Impossible
not-le-ten p = suc≰zero zero p

-- A comparison that answers `true` too often -- a rounding mode that loses
-- the negative verdict, or a default-accept fast path -- cannot meet the
-- `Checkable` obligation, because its reflection law would prove that
-- every integer is below every other.
no-always-true : ((x y : ℤ) -> x ≤ℤ y) -> Impossible
no-always-true all-le = not-le-ten (all-le (mk (suc zero)) (mk zero))

-- ── a worked scan ─────────────────────────────────────────────────────────

-- Literal inequality proofs.  `≤ℤ` on `mk` literals normalises to `≤ℕ` on
-- the corresponding naturals, so these are just successor chains.
≤ℤ-5-7 : mk 5 ≤ℤ mk 7
≤ℤ-5-7 = ≤ℕ-plus 5 2

≤ℤ-5-9 : mk 5 ≤ℤ mk 9
≤ℤ-5-9 = ≤ℕ-plus 5 4

≤ℤ-2-2 : mk 2 ≤ℤ mk 2
≤ℤ-2-2 = ≤ℕ-refl 2

≤ℤ-1-2 : mk 1 ≤ℤ mk 2
≤ℤ-1-2 = ≤ℕ-plus 1 1

-- Four remaining clusters (r = 4, so the coefficient is r - 2 = 2); row
-- sum t(i) = 1; running maximum t(max) = 2; the smallest unexamined
-- distance in row i is 5; the incumbent is q(min) = 0.
--
--     qBound = (r - 2)·5 - 1 - 2 = 10 - 3 = 7 ≥ 0 = q(min)
--
-- so the bound cannot be improved by anything further down the row.
example-suffix : List Entry
example-suffix = entry 3 (mk 7) (mk 2) ∷ entry 4 (mk 9) (mk 1) ∷ []

example-state : ScanState
example-state = scanning (numbers 2 (mk 1) (mk 2) (mk 0))
                         (entry 2 (mk 5) (mk 1))
                         example-suffix

-- The invariants and the accepted check.  The check witnesses
-- `7 ≥ 0` by computation (`decide-ℤ` normalises to `true`).
example-evidence : SkipEvidence ℤ-checkable example-state
example-evidence =
  allCons ≤ℤ-5-7 (allCons ≤ℤ-5-9 allNil)
  , allCons ≤ℤ-2-2 (allCons ≤ℤ-1-2 allNil)
  , refl

-- The claim the run generates, for every entry of the skipped suffix.
example-claim : (e : Entry) -> e ∈E example-suffix ->
  mk 0 ≤ℤ Q 2 (mk 1) (Entry.rowSum e) (Entry.dist e)
example-claim =
  skip-known Standpoint pruned ℤ-checkable example-state example-evidence

-- Spot check: the first skipped entry, to which the bound was compared.
-- Its q-value is (2·7 - 1 - 2) = 11, comfortably above the incumbent.
example-spot : mk 0 ≤ℤ Q 2 (mk 1) (mk 2) (mk 7)
example-spot = example-claim (entry 3 (mk 7) (mk 2)) here

-- ── the status mirror ─────────────────────────────────────────────────────

-- The runtime's `epi_status` vocabulary, named exactly as
-- `EpistemicTypes.jl` spells it (`src/core/Epistemic.jl`).
data Status : Set where
  factive    : Status   -- a verified receipt whose gates were passed
  belief     : Status   -- a receipt without a soundness map
  collapsed  : Status   -- a verified receipt whose gates were not passed
  sans-fibre : Status   -- no verified receipt at all

-- `epi_status`: verify the receipt, then run the gates, then read the rank.
skipStatus : (receiptVerified gatesAccepted : Bool) -> Status
skipStatus false _ = sans-fibre
skipStatus true false = collapsed
skipStatus true true = factive

-- Holding the evidence *is* verifying the receipt; holding the accepted
-- check *is* passing the gate.  Hence:
status-of-skip : {C : Checkable} {s : ScanState} -> SkipEvidence C s -> Status
status-of-skip ev = skipStatus true true

-- A check that was accepted by an exact comparison is `:Factive`, not
-- `:Belief` -- and `RapidNJSkip.no-receipt-reflection` shows why the
-- evidence alone would have been only `:Belief`: a token does not imply
-- the claim.
status-of-skip-is-factive : {C : Checkable} {s : ScanState}
  (ev : SkipEvidence C s) -> status-of-skip {C} {s} ev ≡ factive
status-of-skip-is-factive ev = refl
