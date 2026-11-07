{-# OPTIONS --safe --without-K --cubical-compatible --exact-split --no-sized-types --no-guardedness #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

module QueryIgnoresCollision where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Maybe using (just)
open import Agda.Builtin.Sigma using (_,_; snd)
open import Agda.Builtin.Unit using (tt)
open import EpistemicTypes.QueryRecovery using (QueryRecovery)
open import EpistemicTypes.QueryRecoveryExamples using (publicRetention; publicQuery)

control : QueryRecovery.answer publicQuery true tt ≡ just true
control = refl

-- EXPECTED-REJECTION
-- The second component cannot be recovered after the retention drops it.
forged : QueryRecovery publicRetention snd
QueryRecovery.answer forged _ _ = just false
QueryRecovery.adequate forged (_ , true) = refl
QueryRecovery.adequate forged (_ , false) = refl
