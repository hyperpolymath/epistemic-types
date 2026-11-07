{-# OPTIONS --safe --without-K --cubical-compatible --exact-split --no-sized-types --no-guardedness #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

module EpistemicTypes.ObserverSafety where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Maybe using (Maybe; just)
open import EpistemicTypes.EchoBridge using (Retention)
open import EpistemicTypes.PartialRecovery using (retainedPair; withDefault)
open import EpistemicTypes.QueryRecovery using (QueryRecovery; queryConstant)

private
  sym : {A : Set} {x y : A} -> x ≡ y -> y ≡ x
  sym refl = refl

  trans : {A : Set} {x y z : A} -> x ≡ y -> y ≡ z -> x ≡ z
  trans refl p = p

  cong : {A B : Set} (f : A -> B) {x y : A} -> x ≡ y -> f x ≡ f y
  cong f refl = refl

-- An explicit deterministic observation of the whole Maybe result, including
-- success/failure if see exposes it. These results concern GENERATED inputs.
-- E is a supplied relation; no unproved equivalence laws are silently assumed.
ObservationNI : {A B R T O : Set} {C : Retention A B R} {q : A -> T} ->
  QueryRecovery C q -> (Maybe T -> O) -> (A -> A -> Set) -> Set
ObservationNI {C = C} rec see E = ∀ {x z} -> E x z ->
  see (QueryRecovery.answer rec (Retention.observe C x) (Retention.retain C x)) ≡
  see (QueryRecovery.answer rec (Retention.observe C z) (Retention.retain C z))

ReleaseInvariant : {A T O : Set} -> (A -> T) -> (Maybe T -> O) ->
  (A -> A -> Set) -> Set
ReleaseInvariant q see E = ∀ {x z} -> E x z -> see (just (q x)) ≡ see (just (q z))

releaseInvariantToNI : {A B R T O : Set} {C : Retention A B R} {q : A -> T}
  (rec : QueryRecovery C q) (see : Maybe T -> O) (E : A -> A -> Set) ->
  ReleaseInvariant q see E -> ObservationNI rec see E
releaseInvariantToNI rec see E invariant {x} {z} related =
  trans (cong see (QueryRecovery.adequate rec x))
    (trans (invariant related) (sym (cong see (QueryRecovery.adequate rec z))))

niToReleaseInvariant : {A B R T O : Set} {C : Retention A B R} {q : A -> T}
  (rec : QueryRecovery C q) (see : Maybe T -> O) (E : A -> A -> Set) ->
  ObservationNI rec see E -> ReleaseInvariant q see E
niToReleaseInvariant rec see E invariant {x} {z} related =
  trans (sym (cong see (QueryRecovery.adequate rec x)))
    (trans (invariant related) (cong see (QueryRecovery.adequate rec z)))

-- When the whole answer is visible, related sources must have equal queries.
transparentNIForcesQueryAgreement : {A B R T : Set} {C : Retention A B R} {q : A -> T}
  (rec : QueryRecovery C q) (E : A -> A -> Set) ->
  ObservationNI rec (λ result -> result) E -> ∀ {x z} -> E x z -> q x ≡ q z
transparentNIForcesQueryAgreement {q = q} rec E ni {x} related =
  cong (withDefault (q x)) (niToReleaseInvariant rec (λ result -> result) E ni related)

-- Taking the query to be the whole source rules out hiding a genuinely
-- distinct related pair from an observer who sees that recovered source.
fullRecoveryNIForcesEquality : {A B R : Set} {C : Retention A B R}
  (rec : QueryRecovery C (λ x -> x)) (E : A -> A -> Set) ->
  ObservationNI rec (λ result -> result) E -> ∀ {x z} -> E x z -> x ≡ z
fullRecoveryNIForcesEquality = transparentNIForcesQueryAgreement

-- A separate INPUT-side assumption: if the actual pair hides a relation,
-- every adequate query must respect it. A private residue need not satisfy
-- this assumption merely because the visible projection does.
hiddenPairForcesQueryAgreement : {A B R T : Set} {C : Retention A B R} {q : A -> T}
  (rec : QueryRecovery C q) (E : A -> A -> Set) ->
  (∀ {x z} -> E x z -> retainedPair C x ≡ retainedPair C z) ->
  ∀ {x z} -> E x z -> q x ≡ q z
hiddenPairForcesQueryAgreement rec E hides related = queryConstant rec (hides related)
