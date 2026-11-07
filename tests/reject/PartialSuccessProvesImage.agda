{-# OPTIONS --safe --without-K --cubical-compatible --exact-split --no-sized-types --no-guardedness #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

module PartialSuccessProvesImage where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (_,_)
open import Agda.Builtin.Unit using (tt)
open import EpistemicTypes.PartialRecovery using (retainedPair)
open import EpistemicTypes.PartialRecoveryExamples using (finiteRetention; offImageSuccess)

-- offImageSuccess is checked, yet the successful source does not reproduce
-- this unreachable pair. Success alone cannot establish the stronger law.
forgedCompatibility : retainedPair finiteRetention false ≡ ((false , true) , tt)
forgedCompatibility = refl
