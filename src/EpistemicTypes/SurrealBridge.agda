{-# OPTIONS --safe --without-K #-}

module EpistemicTypes.SurrealBridge where

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Agda.Builtin.Equality using (refl)

open import EpistemicTypes.Access
open import EpistemicTypes.Base
open import EpistemicTypes.Warrant

data Empty : Set where

Not : {ℓ : Level} -> Set ℓ -> Set ℓ
Not A = A -> Empty

-- A set-sized surrogate for surreal standpoints.
--
-- This is deliberately not the full Conway class of all surreal numbers.
-- It may be read as a day-bounded fragment, a chosen universe-level carrier,
-- or any model whose elements are being used as surreal-like epistemic
-- standpoints.
record SurrealSet {sℓ oℓ : Level} : Set (lsuc (sℓ ⊔ oℓ)) where
  infix 4 _≤♯_
  field
    Carrier : Set sℓ
    _≤♯_    : Carrier -> Carrier -> Set oℓ
    refl♯   : {x : Carrier} -> x ≤♯ x
    trans♯  :
      {x y z : Carrier} ->
      x ≤♯ y ->
      y ≤♯ z ->
      x ≤♯ z

-- The surreal order becomes the epistemic access preorder.
-- Reading: x ≤♯ y means y is at least as informed/refined as x.
surrealPreorder :
  {sℓ oℓ : Level} ->
  (S : SurrealSet {sℓ = sℓ} {oℓ = oℓ}) ->
  Preorder {rℓ = oℓ} (SurrealSet.Carrier S)
Preorder._≤κ_ (surrealPreorder S) = SurrealSet._≤♯_ S
Preorder.refl≤ (surrealPreorder S) = SurrealSet.refl♯ S
Preorder.trans≤ (surrealPreorder S) = SurrealSet.trans♯ S

-- Knowledge over surreal standpoints is factive only because this particular
-- instance chooses E x A = A.  The proof is not a theorem about all epistemic
-- modalities over surreal standpoints.
surrealKnowledge :
  {sℓ oℓ ℓ : Level} ->
  (S : SurrealSet {sℓ = sℓ} {oℓ = oℓ}) ->
  FactiveModality (SurrealSet.Carrier S) ℓ
FactiveModality.modality (surrealKnowledge S) =
  record
    { E = λ x A -> A
    ; map = λ f a -> f a
    }
FactiveModality.reflect (surrealKnowledge S) a = a

surrealKnowledgeAccess :
  {sℓ oℓ ℓ : Level} ->
  (S : SurrealSet {sℓ = sℓ} {oℓ = oℓ}) ->
  AccessibleModality {rℓ = oℓ} (SurrealSet.Carrier S) ℓ
AccessibleModality.modality (surrealKnowledgeAccess S) =
  FactiveModality.modality (surrealKnowledge S)
AccessibleModality.access (surrealKnowledgeAccess S) =
  surrealPreorder S
AccessibleModality.increase (surrealKnowledgeAccess S) p a = a
AccessibleModality.increase-refl (surrealKnowledgeAccess S) a = refl
AccessibleModality.increase-trans (surrealKnowledgeAccess S) p q a = refl

-- Belief over surreal standpoints remains non-factive.
-- A token can record that a belief is present without containing A.
data SurrealBelief {sℓ : Level} {K : Set sℓ}
  (x : K) (A : Set) : Set where
  belief-token : SurrealBelief x A

surreal-belief-map :
  {sℓ : Level} {K : Set sℓ} {x : K} {A B : Set} ->
  (A -> B) ->
  SurrealBelief x A ->
  SurrealBelief x B
surreal-belief-map f belief-token = belief-token

surrealBelief :
  {sℓ oℓ : Level} ->
  (S : SurrealSet {sℓ = sℓ} {oℓ = oℓ}) ->
  BeliefModality (SurrealSet.Carrier S) lzero
BeliefModality.modality (surrealBelief S) =
  record
    { E = SurrealBelief
    ; map = surreal-belief-map
    }

no-surreal-belief-reflection :
  {sℓ oℓ : Level} ->
  (S : SurrealSet {sℓ = sℓ} {oℓ = oℓ}) ->
  (x : SurrealSet.Carrier S) ->
  Not ((A : Set) -> SurrealBelief x A -> A)
no-surreal-belief-reflection S x reflectBelief =
  reflectBelief Empty belief-token

-- Warrant over surreal standpoints also remains non-factive unless soundness
-- is provided separately.
data SurrealReceipt : Set where
  surreal-receipt : SurrealReceipt

surrealWarrant :
  {sℓ oℓ : Level} ->
  (S : SurrealSet {sℓ = sℓ} {oℓ = oℓ}) ->
  (x : SurrealSet.Carrier S) ->
  Warrant {wℓ = lzero} (SurrealSet.Carrier S) x Empty
Warrant.Evidence (surrealWarrant S x) = SurrealReceipt

surrealEpi :
  {sℓ oℓ : Level} ->
  (S : SurrealSet {sℓ = sℓ} {oℓ = oℓ}) ->
  (x : SurrealSet.Carrier S) ->
  Epi {wℓ = lzero} (SurrealSet.Carrier S) x Empty
surrealEpi S x = epi (surrealWarrant S x) surreal-receipt

no-surreal-epi-reflection :
  {sℓ oℓ : Level} ->
  (S : SurrealSet {sℓ = sℓ} {oℓ = oℓ}) ->
  (x : SurrealSet.Carrier S) ->
  Not ((A : Set) -> Epi {wℓ = lzero} (SurrealSet.Carrier S) x A -> A)
no-surreal-epi-reflection S x reflectEpi =
  reflectEpi Empty (surrealEpi S x)
