{-# OPTIONS --safe --without-K --cubical-compatible --exact-split --no-sized-types --no-guardedness #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

module CollidingPartialRecovery where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (refl)
open import Agda.Builtin.Maybe using (just)
open import EpistemicTypes.PartialRecovery using (PartialRecovery)
open import EpistemicTypes.PartialRecoveryExamples using (collisionRetention)

forged : PartialRecovery collisionRetention
PartialRecovery.decode forged _ _ = just false
PartialRecovery.roundtrip forged false = refl
PartialRecovery.roundtrip forged true = refl
