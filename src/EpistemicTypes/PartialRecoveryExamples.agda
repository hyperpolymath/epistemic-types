{-# OPTIONS --safe --without-K --cubical-compatible --exact-split --no-sized-types --no-guardedness #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

module EpistemicTypes.PartialRecoveryExamples where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Maybe using (just; nothing)
open import Agda.Builtin.Sigma using (Σ; _,_; fst; snd)
open import Agda.Builtin.Unit using (⊤; tt)
open import EpistemicTypes.EchoBridge using (Retention; Recovery; Impossible)
open import EpistemicTypes.PartialRecovery

private
  cong : {A B : Set} (f : A -> B) {x y : A} -> x ≡ y -> f x ≡ f y
  cong f refl = refl

  falseNotTrue : false ≡ true -> Impossible
  falseNotTrue ()

-- Two generated pairs and two unreachable visible values: the image
-- decision is a finite, explicit computation, with both branches checked.
Visible : Set
Visible = Σ Bool (λ _ -> Bool)

finiteRetention : Retention Bool Visible ⊤
Retention.observe finiteRetention b = b , false
Retention.retain finiteRetention _ = tt
Retention.Cert finiteRetention _ _ = ⊤
Retention.sound finiteRetention _ = tt

finiteSeparates : Separates finiteRetention
finiteSeparates same = cong (λ pair -> fst (fst pair)) same

finiteImageDecision : ImageDecision finiteRetention
finiteImageDecision (b , false) tt = yes (b , refl)
finiteImageDecision (b , true) tt = no
  (λ witness -> falseNotTrue (cong (λ pair -> snd (fst pair)) (snd witness)))

finitePartial : PartialRecovery finiteRetention
finitePartial = fromImageDecision {C = finiteRetention} finiteSeparates finiteImageDecision

finiteGenerated : (b : Bool) ->
  PartialRecovery.decode finitePartial (b , false) tt ≡ just b
finiteGenerated b = refl

finiteUnreachable : (b : Bool) ->
  PartialRecovery.decode finitePartial (b , true) tt ≡ nothing
finiteUnreachable b = refl

finiteSound : SuccessSound finitePartial
finiteSound = imageDecisionSound {C = finiteRetention} finiteSeparates finiteImageDecision

reconstructedDecision : ImageDecision finiteRetention
reconstructedDecision = soundPartialDecidesImage finitePartial finiteSound

private
  positive : {P : Set} -> Decision P -> Bool
  positive (yes _) = true
  positive (no _) = false

reconstructedGenerated : (b : Bool) ->
  positive (reconstructedDecision (b , false) tt) ≡ true
reconstructedGenerated b = refl

reconstructedUnreachable : (b : Bool) ->
  positive (reconstructedDecision (b , true) tt) ≡ false
reconstructedUnreachable b = refl

falseDefault : Recovery finiteRetention
falseDefault = partialToTotal false finitePartial

trueDefault : Recovery finiteRetention
trueDefault = partialToTotal true finitePartial

defaultsAgreeOnImage : (b : Bool) ->
  Recovery.recover falseDefault (b , false) tt ≡ Recovery.recover trueDefault (b , false) tt
defaultsAgreeOnImage b = refl

defaultsDifferOffImage :
  Recovery.recover falseDefault (false , true) tt ≡
  Recovery.recover trueDefault (false , true) tt -> Impossible
defaultsDifferOffImage = falseNotTrue

-- General PartialRecovery deliberately allows success off the image.
-- The chosen total decoder satisfies roundtrip but not a global right inverse.
projectionRecovery : Recovery finiteRetention
Recovery.recover projectionRecovery y _ = fst y
Recovery.roundtrip projectionRecovery _ = refl

offImageSuccess :
  PartialRecovery.decode (totalToPartial projectionRecovery) (false , true) tt ≡ just false
offImageSuccess = refl

offImageIncompatible : retainedPair finiteRetention false ≡ ((false , true) , tt) -> Impossible
offImageIncompatible same = falseNotTrue (cong (λ pair -> snd (fst pair)) same)

-- Empty source makes the partial law vacuous, while the total signature
-- would have to produce an impossible source at the singleton input pair.
emptyRetention : Retention Impossible ⊤ ⊤
Retention.observe emptyRetention ()
Retention.retain emptyRetention ()
Retention.Cert emptyRetention _ _ = Impossible
Retention.sound emptyRetention ()

emptyPartial : PartialRecovery emptyRetention
PartialRecovery.decode emptyPartial _ _ = nothing
PartialRecovery.roundtrip emptyPartial ()

noEmptyTotal : Recovery emptyRetention -> Impossible
noEmptyTotal rec = Recovery.recover rec tt tt

-- Dropping the residue loses the Boolean distinction. A proof-relevant
-- fibre still carries either source, so projection trivially "roundtrips".
-- Its dependence on that supplied witness prevents pair-only recovery.
collisionRetention : Retention Bool ⊤ ⊤
Retention.observe collisionRetention _ = tt
Retention.retain collisionRetention _ = tt
Retention.Cert collisionRetention _ _ = ⊤
Retention.sound collisionRetention _ = tt

witnessProjection : Image collisionRetention tt tt -> Bool
witnessProjection = fst

witnessProjectionRoundtrip : (b : Bool) -> witnessProjection (b , refl) ≡ b
witnessProjectionRoundtrip b = refl

witnessProjectionDependsOnWitness :
  witnessProjection (false , refl) ≡ witnessProjection (true , refl) -> Impossible
witnessProjectionDependsOnWitness = falseNotTrue

noCollidingPartial : PartialRecovery collisionRetention -> Impossible
noCollidingPartial rec = falseNotTrue (partialSeparates rec {false} {true} refl)
