{-# OPTIONS --safe --without-K --cubical-compatible --exact-split --no-sized-types --no-guardedness #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
--
-- The non-factive model.  Two worlds, one standpoint, access only from w₀
-- to w₁.  At w₀ the standpoint has a warrant (a Box proof) for "we are at
-- w₁", and it is false.  So Warrant and SoundWarrant genuinely differ:
-- there is no soundness field for this evidence, provably.
module EpistemicTypes.Kripke.Belief where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Agda.Builtin.Unit using (⊤; tt)
open import EpistemicTypes.Warrant
open import EpistemicTypes.Kripke.Frame

data W : Set where
  w₀ w₁ : W

data _∼_ : W → W → Set where
  w₀∼w₁ : w₀ ∼ w₁

F : Frame ⊤ W
F = record { _∼[_]_ = λ w _ w' → w ∼ w' }

AtW₁ : W → Set
AtW₁ w₀ = ⊥
AtW₁ w₁ = ⊤

-- Warranted at w₀ ...
believed : Box F tt AtW₁ w₀
believed w₁ w₀∼w₁ = tt

-- ... and false at w₀.
false-at-w₀ : ¬ AtW₁ w₀
false-at-w₀ ()

-- epistemic-types' Warrant with this evidence exists; a SoundWarrant with
-- this evidence cannot.
warrant : Warrant ⊤ tt (AtW₁ w₀)
warrant = mkWarrant (Box F tt AtW₁ w₀)

no-sound-warrant : ¬ (Warrant.Evidence warrant → AtW₁ w₀)
no-sound-warrant sound = false-at-w₀ (sound believed)

-- The frame is not reflexive — which is the whole explanation.
not-reflexive : ¬ Reflexive F
not-reflexive r with r tt w₀
... | ()
