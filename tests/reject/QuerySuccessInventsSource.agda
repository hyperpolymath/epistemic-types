{-# OPTIONS --safe --without-K --cubical-compatible --exact-split --no-sized-types --no-guardedness #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

module QuerySuccessInventsSource where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Maybe using (just)
open import Agda.Builtin.Sigma using (_,_)
open import Agda.Builtin.Unit using (tt)
open import EpistemicTypes.PartialRecovery using (Image)
open import EpistemicTypes.PartialRecoveryExamples using (finiteRetention)
open import EpistemicTypes.QueryRecovery using (QueryRecovery)
open import EpistemicTypes.QueryRecoveryExamples using (constantQuery)

control : QueryRecovery.answer (constantQuery finiteRetention) (false , true) tt ≡ just tt
control = refl

-- EXPECTED-REJECTION
-- A successful constant answer cannot invent a source for an off-image pair.
forged : Image finiteRetention (false , true) tt
forged = false , refl
