{-# OPTIONS --safe --without-K --cubical-compatible --exact-split --no-sized-types --no-guardedness #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
--
-- Kripke frames, the box modality, and the frame-condition correspondences
-- the README lists as unformalised.  Constructive throughout; where a
-- converse needs classical reasoning (5, D) it is not claimed.
module EpistemicTypes.Kripke.Frame where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import EpistemicTypes.Kripke.Indexed

data ⊥ : Set where
¬_ : Set → Set
¬ A = A → ⊥

record Frame (K W : Set) : Set₁ where
  field
    _∼[_]_ : W → K → W → Set        -- w ∼[ κ ] w' : κ cannot tell w from w'

module _ {K W : Set} (F : Frame K W) where
  open Frame F

  -- Box: true at every world the standpoint cannot distinguish.
  Box : K → (W → Set) → W → Set
  Box κ φ w = ∀ w' → w ∼[ κ ] w' → φ w'

  box : IndexedModality K W
  box = record { E = Box ; map = λ f w b w' r → f w' (b w' r) }

  ----------------------------------------------------------------------
  -- Frame conditions
  Reflexive  = ∀ κ w → w ∼[ κ ] w
  Transitive = ∀ κ {w w' w''} → w ∼[ κ ] w' → w' ∼[ κ ] w'' → w ∼[ κ ] w''
  Euclidean  = ∀ κ {w w' w''} → w ∼[ κ ] w' → w ∼[ κ ] w'' → w' ∼[ κ ] w''
  Serial     = ∀ κ w → Σ W (λ w' → w ∼[ κ ] w')

  -- T: reflexive frames are exactly the factive ones (both directions).
  T : Reflexive → ∀ κ φ w → Box κ φ w → φ w
  T r κ φ w b = b w (r κ w)

  T⁻¹ : (∀ κ φ w → Box κ φ w → φ w) → Reflexive
  T⁻¹ t κ w = t κ (λ w' → w ∼[ κ ] w') w (λ w' r → r)

  factive : Reflexive → IndexedFactive K W
  factive r = record { modality = box ; reflect = λ {κ} {φ} w b → T r κ φ w b }

  -- 4: transitive frames are exactly the positively introspective ones.
  Four : Transitive → ∀ κ φ w → Box κ φ w → Box κ (Box κ φ) w
  Four t κ φ w b w' r w'' r' = b w'' (t κ r r')

  Four⁻¹ : (∀ κ φ w → Box κ φ w → Box κ (Box κ φ) w) → Transitive
  Four⁻¹ f κ {w} {w'} {w''} r r' = f κ (λ v → w ∼[ κ ] v) w (λ v s → s) w' r w'' r'

  -- 5 and D, one direction (the converses are classical).
  Five : Euclidean → ∀ κ φ w → ¬ Box κ φ w → Box κ (λ w' → ¬ Box κ φ w') w
  Five e κ φ w nb w' r b' = nb (λ w'' r' → b' w'' (e κ r r'))

  D : Serial → ∀ κ φ w → Box κ φ w → ¬ Box κ (λ w' → ¬ φ w') w
  D s κ φ w b nb with s κ w
  ... | w' , r = nb w' r (b w' r)
