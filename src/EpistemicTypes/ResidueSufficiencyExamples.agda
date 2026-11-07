{-# OPTIONS --safe --without-K --cubical-compatible --exact-split --no-sized-types --no-guardedness #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

module EpistemicTypes.ResidueSufficiencyExamples where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (Σ; _,_; fst)
open import Agda.Builtin.Unit using (⊤; tt)
open import EpistemicTypes.EchoBridge using (Impossible)
open import EpistemicTypes.ResidueSufficiency

private
  sym : {A : Set} {x y : A} -> x ≡ y -> y ≡ x
  sym refl = refl

  trans : {A : Set} {x y z : A} -> x ≡ y -> y ≡ z -> x ≡ z
  trans refl p = p

  falseNotTrue : false ≡ true -> Impossible
  falseNotTrue ()

silent : Bool -> ⊤
silent _ = tt

duplicate : Bool -> Σ Bool (λ _ -> Bool)
duplicate b = b , b

singleFromDuplicate : RelativeReduction silent (λ b -> b) duplicate
RelativeReduction.reduce singleFromDuplicate _ = fst
RelativeReduction.realizes singleFromDuplicate _ = refl

duplicateFromSingle : RelativeReduction silent duplicate (λ b -> b)
RelativeReduction.reduce duplicateFromSingle _ b = duplicate b
RelativeReduction.realizes duplicateFromSingle _ = refl

-- Mutual semantic simulation does not make the carriers/encodings identical.
-- No machine representation or bit cost is defined by these declarations.
singleRoundtrip : RelativeReduction silent (λ b -> b) (λ b -> b)
singleRoundtrip = relativeTrans singleFromDuplicate duplicateFromSingle

-- Visible information matters: the identity visible value makes a unit
-- residue adequate, while the same unit residue with silent visibility fails.
visibleSuppliesBit : RelativeReduction (λ b -> b) (λ b -> b) silent
RelativeReduction.reduce visibleSuppliesBit b _ = b
RelativeReduction.realizes visibleSuppliesBit _ = refl

silentCannotSupplyBit : RelativeReduction silent (λ b -> b) silent -> Impossible
silentCannotSupplyBit reduction = falseNotTrue
  (trans (sym (RelativeReduction.realizes reduction false))
    (RelativeReduction.realizes reduction true))
