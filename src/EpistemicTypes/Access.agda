{-# OPTIONS --safe --without-K #-}

module EpistemicTypes.Access where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Equality using (_≡_)

open import EpistemicTypes.Base

-- κ ≤κ κ' reads: κ' is at least as informed as κ, or κ can be accessed
-- from κ'.  The intended transport direction is therefore from κ to κ'.
record Preorder {kℓ rℓ : Level} (K : Set kℓ)
  : Set (kℓ ⊔ lsuc rℓ) where
  infix 4 _≤κ_
  field
    _≤κ_ : K -> K -> Set rℓ
    refl≤ : {κ : K} -> κ ≤κ κ
    trans≤ :
      {κ₀ κ₁ κ₂ : K} ->
      κ₀ ≤κ κ₁ ->
      κ₁ ≤κ κ₂ ->
      κ₀ ≤κ κ₂

-- A modality plus monotone transport along epistemic access.
-- The transport laws are fields because arbitrary E and arbitrary _≤κ_ do not
-- determine them.
record AccessibleModality {kℓ rℓ : Level}
  (K : Set kℓ) (ℓ : Level)
  : Set (kℓ ⊔ lsuc rℓ ⊔ lsuc ℓ) where
  field
    modality : Modality K ℓ
    access   : Preorder {rℓ = rℓ} K

  open Modality modality public
  open Preorder access public

  field
    increase :
      {κ κ' : K} {A : Set ℓ} ->
      κ ≤κ κ' ->
      E κ A ->
      E κ' A

    increase-refl :
      {κ : K} {A : Set ℓ} ->
      (x : E κ A) ->
      increase refl≤ x ≡ x

    increase-trans :
      {κ₀ κ₁ κ₂ : K} {A : Set ℓ} ->
      (p : κ₀ ≤κ κ₁) ->
      (q : κ₁ ≤κ κ₂) ->
      (x : E κ₀ A) ->
      increase q (increase p x) ≡ increase (trans≤ p q) x
