{-# OPTIONS --safe --without-K --cubical-compatible --exact-split --no-sized-types --no-guardedness #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

module ObserverRevealsSecret where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (_,_; fst)
open import EpistemicTypes.QueryRecovery using (mapMaybe)
open import EpistemicTypes.ObserverSafetyExamples using (transparentResult)

control : mapMaybe fst (transparentResult (false , false)) ≡
          mapMaybe fst (transparentResult (false , true))
control = refl

-- EXPECTED-REJECTION
forged : transparentResult (false , false) ≡ transparentResult (false , true)
forged = refl
