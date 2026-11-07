{-# OPTIONS --safe --without-K --cubical-compatible --exact-split --no-sized-types --no-guardedness #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

module OffImageStatusHidden where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Maybe using (just; nothing)
open import Agda.Builtin.Unit using (tt)
open import EpistemicTypes.ObserverSafetyExamples using (requestResult)

reachable : requestResult false ≡ just tt
reachable = refl

unreachable : requestResult true ≡ nothing
unreachable = refl

-- EXPECTED-REJECTION
-- Distinct caller-selected requests; this is not a private-source NI claim.
forged : requestResult false ≡ requestResult true
forged = refl
