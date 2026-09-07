{-# OPTIONS --safe --without-K #-}

module EpistemicTypes.ReadConsistency where

open import Agda.Primitive using (Level; lzero)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import EpistemicTypes.Access using (Preorder)

-- A pure, finite store-history model. A write extends a particular history;
-- its version is derived from that history, not supplied by the caller.
-- This is not a shared-memory implementation or a scheduler-liveness proof.
data Store (A : Set) : Set where
  initial : A -> Store A
  write   : Store A -> A -> Store A

Version : Set
Version = Nat

version : {A : Set} -> Store A -> Version
version (initial _) = zero
version (write s _) = suc (version s)

contents : {A : Set} -> Store A -> A
contents (initial a) = a
contents (write _ a) = a

data ⊥ : Set where

¬_ : {ℓ : Level} -> Set ℓ -> Set ℓ
¬ A = A -> ⊥

cong : {A B : Set} {x y : A} -> (f : A -> B) -> x ≡ y -> f x ≡ f y
cong f refl = refl

trans : {A : Set} {x y z : A} -> x ≡ y -> y ≡ z -> x ≡ z
trans refl q = q

subst : {A : Set} (P : A -> Set) {x y : A} -> x ≡ y -> P x -> P y
subst P refl px = px

data _≤_ : Version -> Version -> Set where
  z≤n : {n : Version} -> zero ≤ n
  s≤s : {m n : Version} -> m ≤ n -> suc m ≤ suc n

≤-refl : {n : Version} -> n ≤ n
≤-refl {zero} = z≤n
≤-refl {suc n} = s≤s ≤-refl

≤-trans : {l m n : Version} -> l ≤ m -> m ≤ n -> l ≤ n
≤-trans z≤n _ = z≤n
≤-trans (s≤s p) (s≤s q) = s≤s (≤-trans p q)

≤-step : {m n : Version} -> m ≤ n -> m ≤ suc n
≤-step z≤n = z≤n
≤-step (s≤s p) = s≤s (≤-step p)

_<_ : Version -> Version -> Set
m < n = suc m ≤ n

<-irrefl : {n : Version} -> ¬ (n < n)
<-irrefl {suc n} (s≤s p) = <-irrefl p

-- Numeric order is a preorder, but does not itself refresh data or evidence.
versionPreorder : Preorder {rℓ = lzero} Version
Preorder._≤κ_ versionPreorder = _≤_
Preorder.refl≤ versionPreorder = ≤-refl
Preorder.trans≤ versionPreorder = ≤-trans

-- An ancestor must belong to this particular history. Equal version numbers
-- on unrelated branches are insufficient.
data _⊑_ {A : Set} : Store A -> Store A -> Set where
  here    : {s : Store A} -> s ⊑ s
  earlier : {s t : Store A} {a : A} -> s ⊑ t -> s ⊑ write t a

ancestorVersions : {A : Set} {s t : Store A} -> s ⊑ t -> version s ≤ version t
ancestorVersions here = ≤-refl
ancestorVersions (earlier p) = ≤-step (ancestorVersions p)

-- Every constructor, including direct client construction, must establish
-- that the observed value matches the indexed store state.
record ReadView {A : Set} (s : Store A) : Set where
  constructor readView
  field
    value   : A
    matches : value ≡ contents s

open ReadView public

readCurrent : {A : Set} (s : Store A) -> ReadView s
readCurrent s = readView (contents s) refl

-- A cached read records its source and its relation to the current history.
record CachedRead {A : Set} (current : Store A) : Set where
  constructor cached
  field
    source   : Store A
    ancestor : source ⊑ current
    view     : ReadView source

open CachedRead public

cachedValue : {A : Set} {s : Store A} -> CachedRead s -> A
cachedValue c = value (view c)

Fresh : {A : Set} {s : Store A} -> CachedRead s -> Set
Fresh {s = s} c = source c ≡ s

Stale : {A : Set} {s : Store A} -> CachedRead s -> Set
Stale {s = s} c = version (source c) < version s

freshImpliesValue : {A : Set} {s : Store A} (c : CachedRead s) ->
  Fresh c -> cachedValue c ≡ contents s
freshImpliesValue (cached _ _ rv) refl = matches rv

freshNotStale : {A : Set} {s : Store A} {c : CachedRead s} ->
  Fresh c -> Stale c -> ⊥
freshNotStale refl st = <-irrefl st

-- This operation actually obtains contents s in the model. Its existence
-- says nothing about whether an external scheduler performs the read.
synchronize : {A : Set} (s : Store A) -> CachedRead s
synchronize s = cached s here (readCurrent s)

syncRestoresFresh : {A : Set} (s : Store A) -> Fresh (synchronize s)
syncRestoresFresh s = refl

syncReadsCurrent : {A : Set} (s : Store A) ->
  cachedValue (synchronize s) ≡ contents s
syncReadsCurrent s = refl

-- Writes do not rewrite cached data. They extend its historical context.
advanceCache : {A : Set} {s : Store A} (a : A) ->
  CachedRead s -> CachedRead (write s a)
advanceCache a (cached origin p rv) = cached origin (earlier p) rv

advancePreservesSample : {A : Set} {s : Store A} (a : A) (c : CachedRead s) ->
  cachedValue (advanceCache a c) ≡ cachedValue c
advancePreservesSample a c = refl

writeStalesCache : {A : Set} {s : Store A} (a : A) (c : CachedRead s) ->
  Stale (advanceCache a c)
writeStalesCache a c = s≤s (ancestorVersions (ancestor c))

writeInvalidatesFreshness : {A : Set} {s : Store A} (a : A) (c : CachedRead s) ->
  ¬ (Fresh (advanceCache a c))
writeInvalidatesFreshness a c fresh =
  freshNotStale {c = advanceCache a c} fresh (writeStalesCache a c)

-- Keeping an old value as a view of a later state requires a real equality.
retainUnchanged : {A : Set} {s t : Store A} -> s ⊑ t ->
  contents s ≡ contents t -> ReadView s -> ReadView t
retainUnchanged _ stable (readView a eq) = readView a (trans eq stable)

-- Evidence about a particular snapshot remains meaningful as historical
-- evidence. Moving it to a new snapshot requires an explicit implication.
FactAt : {A : Set} -> Store A -> (A -> Set) -> Set
FactAt s P = P (contents s)

factFromView : {A : Set} {s : Store A} (P : A -> Set) (rv : ReadView s) ->
  P (value rv) -> FactAt s P
factFromView P rv p = subst P (matches rv) p

transportFact : {A : Set} {s t : Store A} {P : A -> Set} ->
  (P (contents s) -> P (contents t)) -> FactAt s P -> FactAt t P
transportFact preserves p = preserves p

stableFact : {A : Set} {s t : Store A} (P : A -> Set) ->
  contents s ≡ contents t -> FactAt s P -> FactAt t P
stableFact P eq p = subst P eq p

-- A version-only readIncrease / versionAccessible for mutable contents is
-- deliberately absent: an old value need not equal the later store value.
