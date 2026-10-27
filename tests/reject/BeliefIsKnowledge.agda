{-# OPTIONS --safe --without-K --cubical-compatible --exact-split --no-sized-types --no-guardedness #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
module BeliefIsKnowledge where
open import Agda.Builtin.Unit using (⊤; tt)
open import EpistemicTypes.Kripke.Frame
open import EpistemicTypes.Kripke.Belief

-- Must fail: the belief frame is not reflexive, so no factivity.
invalid : Reflexive F
invalid _ w₀ = w₀∼w₁
