{-# OPTIONS --safe --without-K #-}

module EpistemicTypes.Examples where

open import Agda.Primitive using (Level; lzero)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

open import EpistemicTypes.Access
open import EpistemicTypes.Base
open import EpistemicTypes.Warrant

data ⊥ : Set where

¬_ : {ℓ : Level} -> Set ℓ -> Set ℓ
¬ A = A -> ⊥

data Standpoint : Set where
  rough   : Standpoint
  refined : Standpoint
  lab     : Standpoint

-- A tiny preorder: rough information can be refined; refined can be checked
-- by the lab.  Reflexivity and transitivity are explicit constructors/proofs.
data _≤S_ : Standpoint -> Standpoint -> Set where
  id≤          : {κ : Standpoint} -> κ ≤S κ
  rough≤refined : rough ≤S refined
  refined≤lab   : refined ≤S lab
  rough≤lab     : rough ≤S lab

transS :
  {κ₀ κ₁ κ₂ : Standpoint} ->
  κ₀ ≤S κ₁ ->
  κ₁ ≤S κ₂ ->
  κ₀ ≤S κ₂
transS id≤ q = q
transS rough≤refined id≤ = rough≤refined
transS rough≤refined refined≤lab = rough≤lab
transS refined≤lab id≤ = refined≤lab
transS rough≤lab id≤ = rough≤lab

standpointPreorder : Preorder Standpoint
Preorder._≤κ_ standpointPreorder = _≤S_
Preorder.refl≤ standpointPreorder = id≤
Preorder.trans≤ standpointPreorder = transS

-- Knowledge example: this model makes knowledge literally contain A, so it is
-- factive.  This is an example, not a theorem about all modalities.
knowledge : FactiveModality Standpoint lzero
FactiveModality.modality knowledge =
  record
    { E = λ κ A -> A
    ; map = λ f x -> f x
    }
FactiveModality.reflect knowledge x = x

knowledgeAccessible : AccessibleModality Standpoint lzero
AccessibleModality.modality knowledgeAccessible =
  FactiveModality.modality knowledge
AccessibleModality.access knowledgeAccessible = standpointPreorder
AccessibleModality.increase knowledgeAccessible p x = x
AccessibleModality.increase-refl knowledgeAccessible x = refl
AccessibleModality.increase-trans knowledgeAccessible p q x = refl

-- Belief example: a bare report can exist independently of A.
-- There is no reflect field on BeliefModality.
data Belief (κ : Standpoint) (A : Set) : Set where
  hearsay : Bool -> Belief κ A

belief-map :
  {κ : Standpoint} {A B : Set} ->
  (A -> B) ->
  Belief κ A ->
  Belief κ B
belief-map f (hearsay b) = hearsay b

belief : BeliefModality Standpoint lzero
BeliefModality.modality belief =
  record
    { E = Belief
    ; map = belief-map
    }

belief-of-contradiction : Belief rough ⊥
belief-of-contradiction = hearsay true

no-polymorphic-belief-reflection :
  ¬ ((A : Set) -> Belief rough A -> A)
no-polymorphic-belief-reflection reflectBelief =
  reflectBelief ⊥ belief-of-contradiction

-- Observation is introduced only through an explicit observation rule.
-- The base modality does not provide a global return.
data Observation (κ : Standpoint) (A : Set) : Set where
  observed : A -> Observation κ A

observation : Modality Standpoint lzero
Modality.E observation = Observation
Modality.map observation f (observed a) = observed (f a)

record ObservationRule (κ : Standpoint) (A : Set) : Set where
  constructor byObservation
  field
    observed-value : A

observe :
  {κ : Standpoint} {A : Set} ->
  ObservationRule κ A ->
  Observation κ A
observe (byObservation a) = observed a

observed-boolean : Observation refined Bool
observed-boolean = observe (byObservation false)

-- Warrant can be carried for A without exposing A globally.
data LabReceipt : Set where
  receipt-001 : LabReceipt

rough-contradiction-warrant : Warrant Standpoint rough ⊥
Warrant.Evidence rough-contradiction-warrant = LabReceipt

carried-contradiction-warrant : Epi Standpoint rough ⊥
carried-contradiction-warrant =
  epi rough-contradiction-warrant receipt-001

no-polymorphic-epi-reflection :
  ¬ ((A : Set) -> Epi {wℓ = lzero} Standpoint rough A -> A)
no-polymorphic-epi-reflection reflectEpi =
  reflectEpi ⊥ carried-contradiction-warrant

-- Soundness is a separate assumption.  Here a warrant for Bool is sound only
-- because we provide the soundness function explicitly.
bool-warrant : Warrant Standpoint lab Bool
Warrant.Evidence bool-warrant = LabReceipt

sound-bool-warrant : SoundWarrant Standpoint lab Bool
SoundWarrant.warrant sound-bool-warrant = bool-warrant
SoundWarrant.sound sound-bool-warrant receipt-001 = true

sound-bool-example : Bool
sound-bool-example = sound-epi sound-bool-warrant receipt-001
