{-# OPTIONS --safe --without-K --cubical-compatible --exact-split --no-sized-types --no-guardedness #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
--
-- World-indexed modalities.  Base.Modality carries E : K -> Set -> Set,
-- which cannot express Kripke knowledge (truth at every accessible world
-- is a statement about world-indexed propositions; over a single implicit
-- world it collapses to the proposition itself).  The records below are
-- Base/Access field for field, with E indexed by a world type W.  The
-- originals are the W = ⊤ special case (toModality).
module EpistemicTypes.Kripke.Indexed where

open import Agda.Primitive using (lzero)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Unit using (⊤; tt)
open import EpistemicTypes.Base using (Modality)
open import EpistemicTypes.Access using (Preorder)

record IndexedModality (K W : Set) : Set₁ where
  field
    E   : K → (W → Set) → (W → Set)
    map : ∀ {κ A B} → (∀ w → A w → B w) → ∀ w → E κ A w → E κ B w

-- Factive: extraction at the world itself.  Belief-like modalities omit it.
record IndexedFactive (K W : Set) : Set₁ where
  field
    modality : IndexedModality K W
  open IndexedModality modality public
  field
    reflect : ∀ {κ A} w → E κ A w → A w

record IndexedAccessible (K W : Set) : Set₁ where
  field
    modality : IndexedModality K W
    access   : Preorder K
  open IndexedModality modality public
  open Preorder access public
  field
    increase       : ∀ {κ κ' A} → κ ≤κ κ' → ∀ w → E κ A w → E κ' A w
    increase-refl  : ∀ {κ A} w (x : E κ A w) → increase refl≤ w x ≡ x
    increase-trans : ∀ {κ₀ κ₁ κ₂ A} (p : κ₀ ≤κ κ₁) (q : κ₁ ≤κ κ₂) w (x : E κ₀ A w)
                   → increase q w (increase p w x) ≡ increase (trans≤ p q) w x

-- The unindexed record is the one-world case.
toModality : ∀ {K} → IndexedModality K ⊤ → Modality K lzero
toModality M = record
  { E   = λ κ A → IndexedModality.E M κ (λ _ → A) tt
  ; map = λ f → IndexedModality.map M (λ _ → f) tt
  }
