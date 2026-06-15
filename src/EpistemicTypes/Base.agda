{-# OPTIONS --safe --without-K #-}

module EpistemicTypes.Base where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Equality using (_≡_)

-- A bare epistemic modality is an indexed family of endofunctors on Set ℓ.
-- The index κ is a standpoint: an agent, evidence state, accessibility
-- context, warrant regime, or similar epistemic position.
--
-- This record intentionally does not include return/η : A -> E κ A.
-- Such an introduction rule says that truth is epistemically available at κ,
-- which is stronger than a generic modal interface.
record Modality {kℓ : Level} (K : Set kℓ) (ℓ : Level)
  : Set (kℓ ⊔ lsuc ℓ) where
  field
    E   : K -> Set ℓ -> Set ℓ
    map : {κ : K} {A B : Set ℓ} -> (A -> B) -> E κ A -> E κ B

-- Functor laws are not derivable from the type of map in intensional Agda.
-- When a development needs them, it should ask for them as fields.
record LawfulModality {kℓ : Level} (K : Set kℓ) (ℓ : Level)
  : Set (kℓ ⊔ lsuc ℓ) where
  field
    modality : Modality K ℓ

  open Modality modality public

  field
    map-id :
      {κ : K} {A : Set ℓ} ->
      (x : E κ A) ->
      map (λ a -> a) x ≡ x

    map-compose :
      {κ : K} {A B C : Set ℓ} ->
      (f : A -> B) ->
      (g : B -> C) ->
      (x : E κ A) ->
      map g (map f x) ≡ map (λ a -> g (f a)) x

-- Factive modalities have reflection/extraction.
-- Knowledge-like examples may instantiate this record.
record FactiveModality {kℓ : Level} (K : Set kℓ) (ℓ : Level)
  : Set (kℓ ⊔ lsuc ℓ) where
  field
    modality : Modality K ℓ

  open Modality modality public

  field
    reflect : {κ : K} {A : Set ℓ} -> E κ A -> A

-- Belief-like modalities deliberately omit reflect.
-- This is a separate record rather than a factive record with a missing proof.
record BeliefModality {kℓ : Level} (K : Set kℓ) (ℓ : Level)
  : Set (kℓ ⊔ lsuc ℓ) where
  field
    modality : Modality K ℓ

  open Modality modality public

-- A strong introduction rule can be requested explicitly.
-- It is not part of Modality because not every epistemic reading validates it.
record ReturnModality {kℓ : Level} (K : Set kℓ) (ℓ : Level)
  : Set (kℓ ⊔ lsuc ℓ) where
  field
    modality : Modality K ℓ

  open Modality modality public

  field
    return : {κ : K} {A : Set ℓ} -> A -> E κ A
