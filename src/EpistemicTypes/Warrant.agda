{-# OPTIONS --safe --without-K #-}

module EpistemicTypes.Warrant where

open import Agda.Primitive using (Level; lsuc; _⊔_)

-- A warrant is proof-relevant but not automatically sound.
--
-- The parameter A records what the warrant purports to support.  The record
-- exposes only a type of evidence tokens.  There is deliberately no field
-- Evidence -> A here: that would make every warrant factive.
record Warrant {kℓ ℓ wℓ : Level}
  (K : Set kℓ) (κ : K) (A : Set ℓ)
  : Set (kℓ ⊔ ℓ ⊔ lsuc wℓ) where
  constructor mkWarrant
  field
    Evidence : Set wℓ

-- Epi packages an explicit warrant object with a token of that warrant.
-- It is Sigma-like, but specialized so the evidence type is read from the
-- warrant.  Having Epi κ A does not by itself give A.
record Epi {kℓ ℓ wℓ : Level}
  (K : Set kℓ) (κ : K) (A : Set ℓ)
  : Set (kℓ ⊔ ℓ ⊔ lsuc wℓ) where
  constructor epi
  field
    warrant  : Warrant {kℓ = kℓ} {ℓ = ℓ} {wℓ = wℓ} K κ A
    evidence : Warrant.Evidence warrant

-- Sound warrant is a separate assumption.
-- Only after adding the soundness field can one extract A from a token.
record SoundWarrant {kℓ ℓ wℓ : Level}
  (K : Set kℓ) (κ : K) (A : Set ℓ)
  : Set (kℓ ⊔ ℓ ⊔ lsuc wℓ) where
  constructor soundWarrant
  field
    warrant : Warrant {kℓ = kℓ} {ℓ = ℓ} {wℓ = wℓ} K κ A
    sound   : Warrant.Evidence warrant -> A

sound-epi :
  {kℓ ℓ wℓ : Level}
  {K : Set kℓ} {κ : K} {A : Set ℓ} ->
  (sw : SoundWarrant {wℓ = wℓ} K κ A) ->
  Warrant.Evidence (SoundWarrant.warrant sw) ->
  A
sound-epi sw token = SoundWarrant.sound sw token
