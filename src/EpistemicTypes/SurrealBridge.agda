{-# OPTIONS --safe --without-K #-}

module EpistemicTypes.SurrealBridge where

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

open import EpistemicTypes.Access
open import EpistemicTypes.Base
open import EpistemicTypes.EchoBridge using (Echo; Grade; echo; finite; gradePlus)
open import EpistemicTypes.Warrant

data Empty : Set where

Not : {ℓ : Level} -> Set ℓ -> Set ℓ
Not A = A -> Empty

cong :
  {ℓ ℓ' : Level} {A : Set ℓ} {B : Set ℓ'} {x y : A} ->
  (f : A -> B) ->
  x ≡ y ->
  f x ≡ f y
cong f refl = refl

sym : {ℓ : Level} {A : Set ℓ} {x y : A} -> x ≡ y -> y ≡ x
sym refl = refl

-- A set-sized, surreal-like access structure.
--
-- This is still not the full Conway proper class of all surreal numbers.
-- It is a small interface for a day-bounded fragment or chosen carrier of
-- surreal-like standpoints.  Unlike a mere preorder, it must attach a
-- tropical grade to each access proof.  That grade is the formal place where
-- "how much epistemic access is lost/refined between standpoints" lives.
record SurrealAccess {sℓ oℓ : Level} : Set (lsuc (sℓ ⊔ oℓ)) where
  infix 4 _≤♯_
  field
    Carrier : Set sℓ
    _≤♯_    : Carrier -> Carrier -> Set oℓ

    refl♯ :
      {x : Carrier} ->
      x ≤♯ x

    trans♯ :
      {x y z : Carrier} ->
      x ≤♯ y ->
      y ≤♯ z ->
      x ≤♯ z

    magnitude-loss :
      {x y : Carrier} ->
      x ≤♯ y ->
      Grade

    loss-refl :
      {x : Carrier} ->
      magnitude-loss (refl♯ {x = x}) ≡ finite zero

    loss-trans :
      {x y z : Carrier} ->
      (p : x ≤♯ y) ->
      (q : y ≤♯ z) ->
      magnitude-loss (trans♯ p q)
        ≡ gradePlus (magnitude-loss p) (magnitude-loss q)

-- Forgetting the magnitude gives ordinary epistemic accessibility.
-- This direction is honest: every SurrealAccess gives a Preorder, but a
-- Preorder alone is no longer enough to be a SurrealAccess.
surrealPreorder :
  {sℓ oℓ : Level} ->
  (S : SurrealAccess {sℓ = sℓ} {oℓ = oℓ}) ->
  Preorder {rℓ = oℓ} (SurrealAccess.Carrier S)
Preorder._≤κ_ (surrealPreorder S) = SurrealAccess._≤♯_ S
Preorder.refl≤ (surrealPreorder S) = SurrealAccess.refl♯ S
Preorder.trans≤ (surrealPreorder S) = SurrealAccess.trans♯ S

-- Echo retagging preserves the residue while changing the declared loss grade.
-- This is not a recovery of A; it only records that the same residue is now
-- seen after an additional access loss.
retagEcho : {r r' : Grade} {A : Set} -> Echo r A -> Echo r' A
retagEcho (echo Residue residue) = echo Residue residue

-- A modality whose transport across surreal access accumulates access loss
-- into the Echo grade.  This is where the surreal magnitude actually does
-- work in the type.
record GradedSurrealModality {sℓ oℓ : Level}
  (S : SurrealAccess {sℓ = sℓ} {oℓ = oℓ})
  : Set (sℓ ⊔ oℓ ⊔ lsuc (lsuc lzero)) where
  open SurrealAccess S

  field
    modality : Modality Carrier (lsuc lzero)

  open Modality modality public

  field
    transportWithLoss :
      {x y : Carrier} {A : Set} ->
      (p : x ≤♯ y) ->
      (r : Grade) ->
      E x (Echo r A) ->
      E y (Echo (gradePlus r (magnitude-loss p)) A)

-- Factive knowledge over surreal standpoints is still explicit and separate.
surrealKnowledge :
  {sℓ oℓ ℓ : Level} ->
  (S : SurrealAccess {sℓ = sℓ} {oℓ = oℓ}) ->
  FactiveModality (SurrealAccess.Carrier S) ℓ
FactiveModality.modality (surrealKnowledge S) =
  record
    { E = λ x A -> A
    ; map = λ f a -> f a
    }
FactiveModality.reflect (surrealKnowledge S) a = a

surrealKnowledgeAccess :
  {sℓ oℓ ℓ : Level} ->
  (S : SurrealAccess {sℓ = sℓ} {oℓ = oℓ}) ->
  AccessibleModality {rℓ = oℓ} (SurrealAccess.Carrier S) ℓ
AccessibleModality.modality (surrealKnowledgeAccess S) =
  FactiveModality.modality (surrealKnowledge S)
AccessibleModality.access (surrealKnowledgeAccess S) =
  surrealPreorder S
AccessibleModality.increase (surrealKnowledgeAccess S) p a = a
AccessibleModality.increase-refl (surrealKnowledgeAccess S) a = refl
AccessibleModality.increase-trans (surrealKnowledgeAccess S) p q a = refl

-- Identity-on-objects epistemic access to echoes: the value is still only an
-- echo, and crossing access p changes the grade by magnitude-loss p.
surrealEchoKnowledge :
  {sℓ oℓ : Level} ->
  (S : SurrealAccess {sℓ = sℓ} {oℓ = oℓ}) ->
  GradedSurrealModality S
GradedSurrealModality.modality (surrealEchoKnowledge S) =
  record
    { E = λ x A -> A
    ; map = λ f a -> f a
    }
GradedSurrealModality.transportWithLoss (surrealEchoKnowledge S) p r e =
  retagEcho e

-- Belief over surreal standpoints remains non-factive.
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
  (S : SurrealAccess {sℓ = sℓ} {oℓ = oℓ}) ->
  BeliefModality (SurrealAccess.Carrier S) lzero
BeliefModality.modality (surrealBelief S) =
  record
    { E = SurrealBelief
    ; map = surreal-belief-map
    }

no-surreal-belief-reflection :
  {sℓ oℓ : Level} ->
  (S : SurrealAccess {sℓ = sℓ} {oℓ = oℓ}) ->
  (x : SurrealAccess.Carrier S) ->
  Not ((A : Set) -> SurrealBelief x A -> A)
no-surreal-belief-reflection S x reflectBelief =
  reflectBelief Empty belief-token

-- Warrant over surreal standpoints also remains non-factive unless soundness
-- is provided separately.
data SurrealReceipt : Set where
  surreal-receipt : SurrealReceipt

surrealWarrant :
  {sℓ oℓ : Level} ->
  (S : SurrealAccess {sℓ = sℓ} {oℓ = oℓ}) ->
  (x : SurrealAccess.Carrier S) ->
  Warrant {wℓ = lzero} (SurrealAccess.Carrier S) x Empty
Warrant.Evidence (surrealWarrant S x) = SurrealReceipt

surrealEpi :
  {sℓ oℓ : Level} ->
  (S : SurrealAccess {sℓ = sℓ} {oℓ = oℓ}) ->
  (x : SurrealAccess.Carrier S) ->
  Epi {wℓ = lzero} (SurrealAccess.Carrier S) x Empty
surrealEpi S x = epi (surrealWarrant S x) surreal-receipt

no-surreal-epi-reflection :
  {sℓ oℓ : Level} ->
  (S : SurrealAccess {sℓ = sℓ} {oℓ = oℓ}) ->
  (x : SurrealAccess.Carrier S) ->
  Not ((A : Set) -> Epi {wℓ = lzero} (SurrealAccess.Carrier S) x A -> A)
no-surreal-epi-reflection S x reflectEpi =
  reflectEpi Empty (surrealEpi S x)

-- A concrete finite-day fragment.
--
-- This is not the full surreal universe.  It is a tiny model of the birthday
-- tower: n ≤N m means the m-day standpoint is at least as refined as the
-- n-day standpoint, and the access grade is the number of birthday steps
-- between them.
data _≤N_ : Nat -> Nat -> Set where
  z≤n : {n : Nat} -> zero ≤N n
  s≤s : {m n : Nat} -> m ≤N n -> suc m ≤N suc n

refl≤N : {n : Nat} -> n ≤N n
refl≤N {zero} = z≤n
refl≤N {suc n} = s≤s refl≤N

trans≤N : {m n k : Nat} -> m ≤N n -> n ≤N k -> m ≤N k
trans≤N z≤n q = z≤n
trans≤N (s≤s p) (s≤s q) = s≤s (trans≤N p q)

diff≤N : {m n : Nat} -> m ≤N n -> Nat
diff≤N {zero} {n} z≤n = n
diff≤N {suc m} {suc n} (s≤s p) = diff≤N p

diff-refl≤N : {n : Nat} -> diff≤N (refl≤N {n = n}) ≡ zero
diff-refl≤N {zero} = refl
diff-refl≤N {suc n} = diff-refl≤N {n = n}

right-diff≤N : {n k : Nat} -> (q : n ≤N k) -> n + diff≤N q ≡ k
right-diff≤N z≤n = refl
right-diff≤N (s≤s q) = cong suc (right-diff≤N q)

diff-trans≤N :
  {m n k : Nat} ->
  (p : m ≤N n) ->
  (q : n ≤N k) ->
  diff≤N (trans≤N p q) ≡ diff≤N p + diff≤N q
diff-trans≤N z≤n q = sym (right-diff≤N q)
diff-trans≤N (s≤s p) (s≤s q) = diff-trans≤N p q

daySurrealAccess : SurrealAccess {sℓ = lzero} {oℓ = lzero}
SurrealAccess.Carrier daySurrealAccess = Nat
SurrealAccess._≤♯_ daySurrealAccess = _≤N_
SurrealAccess.refl♯ daySurrealAccess = refl≤N
SurrealAccess.trans♯ daySurrealAccess = trans≤N
SurrealAccess.magnitude-loss daySurrealAccess p = finite (diff≤N p)
SurrealAccess.loss-refl daySurrealAccess {x = n} =
  cong finite (diff-refl≤N {n = n})
SurrealAccess.loss-trans daySurrealAccess p q =
  cong finite (diff-trans≤N p q)

two : Nat
two = suc (suc zero)

day-loss-two :
  SurrealAccess.magnitude-loss daySurrealAccess (z≤n {n = two})
    ≡ finite two
day-loss-two = refl
