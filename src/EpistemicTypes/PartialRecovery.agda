{-# OPTIONS --safe --without-K --cubical-compatible --exact-split --no-sized-types --no-guardedness #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

module EpistemicTypes.PartialRecovery where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Maybe using (Maybe; just; nothing)
open import Agda.Builtin.Sigma using (Σ; _,_; fst; snd)
open import EpistemicTypes.EchoBridge using (Retention; Recovery; Impossible)

withDefault : {A : Set} -> A -> Maybe A -> A
withDefault fallback nothing = fallback
withDefault fallback (just x) = x

private
  sym : {A : Set} {x y : A} -> x ≡ y -> y ≡ x
  sym refl = refl

  trans : {A : Set} {x y z : A} -> x ≡ y -> y ≡ z -> x ≡ z
  trans refl q = q

  cong : {A B : Set} (f : A -> B) {x y : A} -> x ≡ y -> f x ≡ f y
  cong f refl = refl

  eliminate : {A : Set} -> Impossible -> A
  eliminate ()

  justInjective : {A : Set} {x y : A} -> just x ≡ just y -> x ≡ y
  justInjective {x = x} = cong (withDefault x)

  nothingNotJust : {A : Set} {x : A} -> nothing ≡ just x -> Impossible
  nothingNotJust ()

retainedPair : {A B R : Set} -> Retention A B R -> A -> Σ B (λ _ -> R)
retainedPair C x = Retention.observe C x , Retention.retain C x

-- This is the standard proof-relevant fibre of the retained-pair function.
-- Its witness CONTAINS a source; projecting that source is not recovery
-- from the visible/residue pair alone. The optional canonical adapter
-- identifies this definition with the owning Echo.Echo, without truncation.
Image : {A B R : Set} -> Retention A B R -> B -> R -> Set
Image {A} C y r = Σ A (λ x -> retainedPair C x ≡ (y , r))

Separates : {A B R : Set} -> Retention A B R -> Set
Separates {A} C = {x z : A} -> retainedPair C x ≡ retainedPair C z -> x ≡ z

-- A decoder is a function of the retained pair ONLY. It receives neither
-- a source witness nor a certificate. Failure is allowed off the image.
-- Roundtrip does NOT require failure off the image: a successful result
-- there need not reproduce its input pair. Soundness is a separate property.
record PartialRecovery {A B R : Set} (C : Retention A B R) : Set where
  field
    decode    : B -> R -> Maybe A
    roundtrip : (x : A) ->
      decode (Retention.observe C x) (Retention.retain C x) ≡ just x

totalToPartial : {A B R : Set} {C : Retention A B R} ->
  Recovery C -> PartialRecovery C
PartialRecovery.decode (totalToPartial rec) y r = just (Recovery.recover rec y r)
PartialRecovery.roundtrip (totalToPartial rec) x = cong just (Recovery.roundtrip rec x)

-- The fallback is explicit data, not an assumed inhabitant or a choice
-- principle. It is irrelevant on generated pairs by the roundtrip law.
partialToTotal : {A B R : Set} {C : Retention A B R} ->
  A -> PartialRecovery C -> Recovery C
Recovery.recover (partialToTotal fallback rec) y r =
  withDefault fallback (PartialRecovery.decode rec y r)
Recovery.roundtrip (partialToTotal fallback rec) x =
  cong (withDefault fallback) (PartialRecovery.roundtrip rec x)

totalPartialDecoder : {A B R : Set} {C : Retention A B R}
  (fallback : A) (rec : Recovery C) (y : B) (r : R) ->
  Recovery.recover (partialToTotal fallback (totalToPartial rec)) y r ≡
  Recovery.recover rec y r
totalPartialDecoder fallback rec y r = refl

partialSeparates : {A B R : Set} {C : Retention A B R} ->
  PartialRecovery C -> Separates C
partialSeparates rec {x} {z} same = justInjective
  (trans (sym (PartialRecovery.roundtrip rec x))
    (trans (cong (λ pair -> PartialRecovery.decode rec (fst pair)
      (snd pair)) same) (PartialRecovery.roundtrip rec z)))

partialComplete : {A B R : Set} {C : Retention A B R}
  (rec : PartialRecovery C) {y : B} {r : R} (witness : Image C y r) ->
  PartialRecovery.decode rec y r ≡ just (fst witness)
partialComplete rec (x , same) =
  trans (sym (cong (λ pair -> PartialRecovery.decode rec (fst pair) (snd pair)) same))
    (PartialRecovery.roundtrip rec x)

-- Independent of roundtrip: every successful output must reproduce the
-- requested pair. Plain PartialRecovery does not promise this property.
SuccessSound : {A B R : Set} {C : Retention A B R} -> PartialRecovery C -> Set
SuccessSound {A} {B} {R} {C} rec = (y : B) (r : R) (x : A) ->
  PartialRecovery.decode rec y r ≡ just x -> retainedPair C x ≡ (y , r)

data Decision (P : Set) : Set where
  yes : P -> Decision P
  no  : (P -> Impossible) -> Decision P

-- A positive answer must provide an actual source and an equality proof.
-- No general decision procedure follows from Separates, Cert or sound.
ImageDecision : {A B R : Set} -> Retention A B R -> Set
ImageDecision {B = B} {R = R} C = (y : B) (r : R) -> Decision (Image C y r)

-- Sound success supplies an image witness; failure refutes all witnesses
-- because roundtrip recovers every member of the image. This is the exact
-- additional premise needed here to obtain a decision from a partial decoder.
soundPartialDecidesImage : {A B R : Set} {C : Retention A B R}
  (rec : PartialRecovery C) -> SuccessSound rec -> ImageDecision C
soundPartialDecidesImage rec sound y r with PartialRecovery.decode rec y r in result
... | just x = yes (x , sound y r x result)
... | nothing = no
  (λ witness -> nothingNotJust (trans (sym result) (partialComplete rec witness)))

private
  imageValue : {A B R : Set} {C : Retention A B R} {y : B} {r : R} ->
    Decision (Image C y r) -> Maybe A
  imageValue (yes (x , _)) = just x
  imageValue (no _) = nothing

-- The decision procedure chooses a witness internally from y and r.
-- Separation proves that every possible positive answer at a generated
-- pair returns the original source. A bare fibre projection lacks this law.
fromImageDecision : {A B R : Set} {C : Retention A B R} ->
  Separates C -> ImageDecision C -> PartialRecovery C
PartialRecovery.decode (fromImageDecision {C = C} separates decide) y r =
  imageValue {C = C} (decide y r)
PartialRecovery.roundtrip (fromImageDecision {C = C} separates decide) x
  with decide (Retention.observe C x) (Retention.retain C x)
... | yes (z , same) = cong just (separates same)
... | no absent = eliminate (absent (x , refl))

-- This stronger property holds for the image-decision construction, but
-- is deliberately not a field of PartialRecovery (totalToPartial would
-- otherwise require an extra right-inverse law on unreachable inputs).
imageDecisionSound : {A B R : Set} {C : Retention A B R}
  (separates : Separates C) (decide : ImageDecision C) ->
  SuccessSound (fromImageDecision {C = C} separates decide)
imageDecisionSound {C = C} separates decide y r x success with decide y r
... | yes (z , same) =
  trans (cong (retainedPair C) (sym (justInjective success))) same
... | no absent = eliminate (nothingNotJust success)

-- Any concrete inhabitant of the fibre is recovered; combined with
-- imageDecisionSound this is a constructive, untruncated characterization
-- of successful decoding by this construction. No equality of proofs is used.
imageDecisionComplete : {A B R : Set} {C : Retention A B R}
  (separates : Separates C) (decide : ImageDecision C)
  {y : B} {r : R} (witness : Image C y r) ->
  PartialRecovery.decode (fromImageDecision {C = C} separates decide) y r ≡ just (fst witness)
imageDecisionComplete {C = C} separates decide =
  partialComplete (fromImageDecision {C = C} separates decide)
