{-# OPTIONS --safe --without-K --cubical-compatible --exact-split --no-sized-types --no-guardedness #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

module CanonicalRecovery where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Fin.Base using (Fin)
open import Data.Nat.Base using (ℕ; _≤_)
open import Relation.Binary.PropositionalEquality using (_≢_)
import EchoFiniteResidue as Finite
open import EpistemicTypes.EchoBridge using (Retention; Recovery)

-- Import the owning definitions. Keep the full retention contract C fixed:
-- neither conversion chooses a certificate nor reconstructs one from recovery.
-- Epistemic's carriers are Set₀; the canonical contract is specialized here.
toExactRecovery : {A B R : Set} {C : Retention A B R} → Recovery C →
  Finite.ExactRecovery (Retention.observe C) (Retention.retain C)
toExactRecovery rec = record
  { recover = Recovery.recover rec
  ; roundtrip = Recovery.roundtrip rec
  }

fromExactRecovery : {A B R : Set} {C : Retention A B R} →
  Finite.ExactRecovery (Retention.observe C) (Retention.retain C) → Recovery C
fromExactRecovery rec = record
  { recover = Finite.ExactRecovery.recover rec
  ; roundtrip = Finite.ExactRecovery.roundtrip rec
  }

-- Record eta suffices, including the proof field. No function extensionality
-- or proof irrelevance is required. These laws preserve the TOTAL decoder,
-- including inputs that no source actually produces.
fromToRecovery : {A B R : Set} {C : Retention A B R} (rec : Recovery C) →
  fromExactRecovery {C = C} (toExactRecovery rec) ≡ rec
fromToRecovery rec = refl

toFromExactRecovery : {A B R : Set} {C : Retention A B R}
  (rec : Finite.ExactRecovery (Retention.observe C) (Retention.retain C)) →
  toExactRecovery (fromExactRecovery {C = C} rec) ≡ rec
toFromExactRecovery rec = refl

decoderAgrees : {A B R : Set} {C : Retention A B R}
  (rec : Recovery C) (y : B) (r : R) →
  Finite.ExactRecovery.recover (toExactRecovery rec) y r ≡ Recovery.recover rec y r
decoderAgrees rec y r = refl

roundtripProofAgrees : {A B R : Set} {C : Retention A B R}
  (rec : Recovery C) (x : A) →
  Finite.ExactRecovery.roundtrip (toExactRecovery rec) x ≡ Recovery.roundtrip rec x
roundtripProofAgrees rec x = refl

-- The existing canonical finite-alphabet theorem now applies to the actual
-- Epistemic observation and retention functions. The selected sources need
-- not enumerate a whole fibre. Cost here is alphabet cardinality only.
recoveryFiniteFibreBound : {A B : Set} {n k : ℕ} {C : Retention A B (Fin k)} →
  Recovery C → (select : Fin n → A) →
  (∀ {i j} → select i ≡ select j → i ≡ j) →
  (y : B) → (∀ i → Retention.observe C (select i) ≡ y) → n ≤ k
recoveryFiniteFibreBound rec = Finite.finite-fibre-bound (toExactRecovery rec)

recoveryForbidsResidueCollision : {A B R : Set} {C : Retention A B R} →
  Recovery C → ∀ {x z} → x ≢ z →
  Retention.observe C x ≡ Retention.observe C z → Retention.retain C x ≢ Retention.retain C z
recoveryForbidsResidueCollision rec =
  Finite.recovery-forbids-residue-collision (toExactRecovery rec)
