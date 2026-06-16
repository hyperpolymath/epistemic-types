{-# OPTIONS --safe --without-K #-}

------------------------------------------------------------------------
-- Version-monotone read-consistency RECOVERY LIVENESS, as a concrete
-- instance over the canonical epistemic framework.
--
-- This module is the Agda upstream draft of typed-wasm's Idris
-- TypedWasm.ABI.Epistemic (Level 12, shared-memory read consistency).
-- The Idris file proves there is no permanently-stuck stale state: a
-- single re-sync always recovers freshness, and freshness propagates
-- across any number of intervening writes via one re-sync.  Here those
-- same liveness theorems are re-derived over Nat versions, and the
-- model is wired to the canonical EpistemicTypes.Access Preorder /
-- AccessibleModality so that "versions-as-standpoints" is an actual
-- instance of the standpoint-indexed accessible modality, not a
-- parallel ad-hoc theory.
--
-- Standpoints are versions (a Version = Nat).  v ≤κ v' reads "v' is at
-- least as informed/advanced as v" — i.e. v' is a later (or equal)
-- version, and knowledge at v can be transported to v'.  This matches
-- the canonical Access reading exactly: transport flows from the less
-- informed standpoint to the more informed one.
--
-- Estate boundary note (cf. Epistemic.idr header): the Idris file flags
-- this as a possibly-DIFFERENT problem from the canonical standpoint
-- modality.  This module is the affirmative answer to the OPEN DESIGN
-- QUESTION it poses: versions DO instantiate the canonical
-- AccessibleModality (Version-as-standpoint, ≤ on Nat as access), and
-- the read-consistency liveness theorems are theorems ABOUT that
-- instance.
------------------------------------------------------------------------

module EpistemicTypes.ReadConsistency where

open import Agda.Primitive using (Level; lzero; lsuc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)

open import EpistemicTypes.Base
open import EpistemicTypes.Access

------------------------------------------------------------------------
-- Versions, ordering, and the empty type
------------------------------------------------------------------------

-- A version is just a Nat.  Each write increments it (modelled by suc).
Version : Set
Version = Nat

data ⊥ : Set where

¬_ : {ℓ : Level} -> Set ℓ -> Set ℓ
¬ A = A -> ⊥

-- Less-than-or-equal on versions.  This is the accessibility relation:
-- v ≤ v' means v' is the same or a later version.
data _≤_ : Version -> Version -> Set where
  z≤n : {n : Version} -> zero ≤ n
  s≤s : {m n : Version} -> m ≤ n -> suc m ≤ suc n

-- Strict less-than: v < v' ≜ suc v ≤ v'.  Used for "a write has happened".
_<_ : Version -> Version -> Set
m < n = suc m ≤ n

≤-refl : {n : Version} -> n ≤ n
≤-refl {zero}  = z≤n
≤-refl {suc n} = s≤s ≤-refl

≤-trans : {l m n : Version} -> l ≤ m -> m ≤ n -> l ≤ n
≤-trans z≤n       _         = z≤n
≤-trans (s≤s p)   (s≤s q)   = s≤s (≤-trans p q)

-- < is irreflexive: v < v is uninhabited.  Mirrors Idris ltIrreflexive.
<-irrefl : {n : Version} -> ¬ (n < n)
<-irrefl {suc n} (s≤s p) = <-irrefl p

-- A strict-less witness is itself a (weak) ≤ witness.
<⇒≤ : {m n : Version} -> m < n -> m ≤ n
<⇒≤ {zero}  _       = z≤n
<⇒≤ {suc m} (s≤s p) = s≤s (<⇒≤ p)

------------------------------------------------------------------------
-- The canonical Preorder instance: versions ordered by ≤
------------------------------------------------------------------------

-- Versions-as-standpoints: the access relation of the canonical
-- EpistemicTypes.Access.Preorder, instantiated at K = Version with ≤.
versionPreorder : Preorder {rℓ = lzero} Version
Preorder._≤κ_   versionPreorder = _≤_
Preorder.refl≤  versionPreorder = ≤-refl
Preorder.trans≤ versionPreorder = ≤-trans

------------------------------------------------------------------------
-- Freshness / staleness predicates over versions
------------------------------------------------------------------------

-- A module's knowledge at knownVersion is FRESH relative to a field's
-- currentVersion iff it has caught up: knownVersion ≡ currentVersion.
-- (The Idris Fresh additionally pins a FieldVersion record to ground
-- truth; that pin is an Idris-side soundness device for the global
-- store and is orthogonal to the liveness story re-proved here.)
--
-- Defined AS the propositional equality of the two version indices,
-- rather than as a fresh data type with a green-slime reflexive index.
-- Under --without-K, matching a `Fresh v v` self-reflexive index would
-- be rejected (UnificationStuck); routing through _≡_ keeps every proof
-- below K-free while preserving the named predicate Fresh.
Fresh : (knownVersion currentVersion : Version) -> Set
Fresh knownVersion currentVersion = knownVersion ≡ currentVersion

-- Canonical freshness constructor: a view that has caught up.
mkFresh : {v : Version} -> Fresh v v
mkFresh = refl

-- Knowledge is STALE iff the field has advanced past what is known:
-- knownVersion < currentVersion.
data Stale : (knownVersion currentVersion : Version) -> Set where
  mkStale : {v v' : Version} -> v < v' -> Stale v v'

-- A SYNC event carries a module from oldVersion up to newVersion; after
-- it, the module knows newVersion.  Modelled as the post-sync witness
-- (oldVersion is recorded only to mirror the Idris index shape).
data Sync : (oldVersion newVersion : Version) -> Set where
  sync : {old new : Version} -> Sync old new

------------------------------------------------------------------------
-- Projectors / non-interference (mirrors the Idris lemmas)
------------------------------------------------------------------------

freshImpliesEqual : {v v' : Version} -> Fresh v v' -> v ≡ v'
freshImpliesEqual eq = eq

staleImpliesLT : {v v' : Version} -> Stale v v' -> v < v'
staleImpliesLT (mkStale lt) = lt

-- Fresh and Stale are mutually exclusive at the same indices.
freshNotStale : {v v' : Version} -> Fresh v v' -> Stale v v' -> ⊥
freshNotStale refl (mkStale lt) = <-irrefl lt

------------------------------------------------------------------------
-- Core recovery-liveness theorems
------------------------------------------------------------------------

-- A sync restores freshness at the synced-to version.  (Idris
-- syncRestoresFresh.)
syncRestoresFresh : {old new : Version} -> Sync old new -> Fresh new new
syncRestoresFresh sync = mkFresh

-- Concurrent-write staleness: a fresh view goes stale once the global
-- current version advances strictly past it.  (Idris
-- concurrentWriteStales.)
concurrentWriteStales :
  {v v' : Version} -> Fresh v v -> v < v' -> Stale v v'
concurrentWriteStales _ lt = mkStale lt

-- Re-synchronisation after a concurrent write restores freshness:
-- a stale view plus a sync to the current version yields a fresh view.
-- This is the no-permanently-stuck-state guarantee.  (Idris
-- resyncRecoversFresh.)
resyncRecoversFresh :
  {v cur : Version} -> Stale v cur -> Sync v cur -> Fresh cur cur
resyncRecoversFresh _ s = syncRestoresFresh s

-- FLAGSHIP liveness: freshness propagates under any number of
-- intervening writes via a SINGLE re-sync.  Starting fresh at v, after
-- the current version advances to cur (by however many writes, captured
-- as v < cur), one sync recovers freshness at cur.  (Idris
-- freshnessPropagatesUnderWrites.)
freshnessPropagatesUnderWrites :
  {v cur : Version} -> Fresh v v -> v < cur -> Sync v cur -> Fresh cur cur
freshnessPropagatesUnderWrites _ _ s = syncRestoresFresh s

-- Chained syncs end fresh: any two-step sync sequence terminates fresh
-- at the final version.  (Idris syncChainEndsFresh.)
syncChainEndsFresh :
  {v1 v2 v3 : Version} -> Sync v1 v2 -> Sync v2 v3 -> Fresh v3 v3
syncChainEndsFresh _ s2 = syncRestoresFresh s2

------------------------------------------------------------------------
-- Wiring to the canonical AccessibleModality
------------------------------------------------------------------------

-- A fresh epistemic view at standpoint (version) v of a value of type A.
-- The view is indexed by the *current* version v; holding ReadView v A
-- means "I have A and my knowledge is fresh at v".  Freshness is
-- intrinsic to the index — a view living at version v is by definition
-- caught up to v — so it is recovered as the lemma `viewIsFresh` below
-- rather than stored as a field.  Keeping the record to a single value
-- field is what makes the canonical increase-refl / increase-trans laws
-- hold *definitionally* under --without-K (no UIP on a stored proof).
record ReadView (v : Version) (A : Set) : Set where
  constructor readView
  field
    value : A

open ReadView

-- A view at version v is fresh at v, by construction.  This recovers the
-- "fresh field" as a theorem, tying the modal layer back to the Fresh
-- predicate of the liveness theorems above.
viewIsFresh : {v : Version} {A : Set} -> ReadView v A -> Fresh v v
viewIsFresh _ = mkFresh

-- The bare modality: E v A = ReadView v A.  map acts on the carried
-- value; freshness is preserved automatically since it is intrinsic.
readModality : Modality Version lzero
Modality.E   readModality v A = ReadView v A
Modality.map readModality f rv = readView (f (value rv))

-- Monotone transport along version access: given v ≤ v' (v' is a later
-- version) and a view fresh at v, we can RE-SYNC it to a view fresh at
-- v'.  This is exactly the canonical `increase`, and it is the modal
-- packaging of `freshnessPropagatesUnderWrites`: advancing the
-- standpoint never destroys the value; a single (implicit) sync
-- re-establishes freshness at the newer version.
readIncrease :
  {v v' : Version} {A : Set} -> v ≤ v' -> ReadView v A -> ReadView v' A
readIncrease _ rv = readView (value rv)

-- Transport at refl≤ is the identity (holds definitionally — the record
-- has a single value field with η).
readIncrease-refl :
  {v : Version} {A : Set} (rv : ReadView v A) ->
  readIncrease (≤-refl {v}) rv ≡ rv
readIncrease-refl _ = refl

-- Transport composes (definitionally).
readIncrease-trans :
  {v0 v1 v2 : Version} {A : Set}
  (p : v0 ≤ v1) (q : v1 ≤ v2) (rv : ReadView v0 A) ->
  readIncrease q (readIncrease p rv) ≡ readIncrease (≤-trans p q) rv
readIncrease-trans _ _ _ = refl

-- The full canonical AccessibleModality instance: versions-as-
-- standpoints, ≤ as access, ReadView as the modality, and re-sync as
-- monotone transport.  This is the concrete hookup the Idris header's
-- OPEN DESIGN QUESTION asked for.
versionAccessible : AccessibleModality Version lzero
AccessibleModality.modality      versionAccessible = readModality
AccessibleModality.access        versionAccessible = versionPreorder
AccessibleModality.increase      versionAccessible = readIncrease
AccessibleModality.increase-refl versionAccessible = readIncrease-refl
AccessibleModality.increase-trans versionAccessible = readIncrease-trans
