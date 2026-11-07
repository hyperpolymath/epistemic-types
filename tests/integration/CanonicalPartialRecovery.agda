{-# OPTIONS --safe --without-K --cubical-compatible --exact-split --no-sized-types --no-guardedness #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

module CanonicalPartialRecovery where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (_,_)
import Echo as Canonical
open import EpistemicTypes.EchoBridge using (Retention)
open import EpistemicTypes.PartialRecovery

-- The builtin Sigma and equality used by Image are the exact types used by
-- canonical Echo. Both maps preserve the source AND the original path.
-- This is a definitional identification of a standard fibre, not a claim
-- that its source can be recovered from a pair without further evidence.
toCanonicalImage : {A B R : Set} {C : Retention A B R} {y : B} {r : R} ->
  Image C y r -> Canonical.Echo (retainedPair C) (y , r)
toCanonicalImage witness = witness

fromCanonicalImage : {A B R : Set} {C : Retention A B R} {y : B} {r : R} ->
  Canonical.Echo (retainedPair C) (y , r) -> Image C y r
fromCanonicalImage witness = witness

imageRoundtrip : {A B R : Set} {C : Retention A B R} {y : B} {r : R}
  (witness : Image C y r) ->
  fromCanonicalImage {C = C} (toCanonicalImage {C = C} witness) ≡ witness
imageRoundtrip witness = refl

canonicalRoundtrip : {A B R : Set} {C : Retention A B R} {y : B} {r : R}
  (witness : Canonical.Echo (retainedPair C) (y , r)) ->
  toCanonicalImage {C = C} (fromCanonicalImage {C = C} witness) ≡ witness
canonicalRoundtrip witness = refl

fromCanonicalDecision : {A B R : Set} {C : Retention A B R} ->
  Separates C ->
  ((y : B) (r : R) -> Decision (Canonical.Echo (retainedPair C) (y , r))) ->
  PartialRecovery C
fromCanonicalDecision {C = C} = fromImageDecision {C = C}
