{-# OPTIONS --safe --without-K --cubical-compatible --exact-split --no-sized-types --no-guardedness #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

module ForgetfulResidueSufficient where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (refl)
open import EpistemicTypes.ResidueSufficiency using (RelativeReduction)
open import EpistemicTypes.ResidueSufficiencyExamples using (silent; visibleSuppliesBit)

control : RelativeReduction (λ b -> b) (λ b -> b) silent
control = visibleSuppliesBit

-- EXPECTED-REJECTION
forged : RelativeReduction silent (λ b -> b) silent
RelativeReduction.reduce forged _ _ = false
RelativeReduction.realizes forged false = refl
RelativeReduction.realizes forged true = refl
