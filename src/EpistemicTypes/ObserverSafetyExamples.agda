{-# OPTIONS --safe --without-K --cubical-compatible --exact-split --no-sized-types --no-guardedness #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

module EpistemicTypes.ObserverSafetyExamples where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Maybe using (Maybe; just; nothing)
open import Agda.Builtin.Sigma using (_,_; fst; snd)
open import Agda.Builtin.Unit using (⊤; tt)
open import EpistemicTypes.EchoBridge using (Retention; Impossible)
open import EpistemicTypes.PartialRecoveryExamples using (finiteRetention; finiteImageDecision)
open import EpistemicTypes.QueryRecovery
open import EpistemicTypes.QueryRecoveryExamples using (Pair)
open import EpistemicTypes.ObserverSafety

private
  cong : {A B : Set} (f : A -> B) {x y : A} -> x ≡ y -> f x ≡ f y
  cong f refl = refl

-- The second bit is privately retained. Publishing only the first bit of
-- the recovered result respects low equivalence; publishing both does not.
privateRetention : Retention Pair Bool Bool
Retention.observe privateRetention = fst
Retention.retain privateRetention = snd
Retention.Cert privateRetention _ _ = ⊤
Retention.sound privateRetention _ = tt

privateRecovery : QueryRecovery privateRetention (λ x -> x)
QueryRecovery.answer privateRecovery b secret = just (b , secret)
QueryRecovery.adequate privateRecovery (b , secret) = refl

LowRelated : Pair -> Pair -> Set
LowRelated x z = fst x ≡ fst z

redactedNI : ObservationNI privateRecovery (mapMaybe fst) LowRelated
redactedNI {x} {z} related = releaseInvariantToNI privateRecovery (mapMaybe fst) LowRelated
  (λ {u} {v} same -> cong just same) {x} {z} related

transparentResult : Pair -> Maybe Pair
transparentResult x = QueryRecovery.answer privateRecovery (fst x) (snd x)

transparentLeak : transparentResult (false , false) ≡ transparentResult (false , true) -> Impossible
transparentLeak ()

noTransparentNI : ObservationNI privateRecovery (λ result -> result) LowRelated -> Impossible
noTransparentNI ni = transparentLeak (ni {false , false} {false , true} refl)

-- Even a constant query can have different statuses on ARBITRARY requests.
-- Here the second request bit selects an unreachable input, rather than a
-- generated pair. This does not contradict generated-input noninterference.
-- Both requests are caller-selected and visible: this example alone is NOT
-- leakage of a private source or a two-run confidentiality counterexample.
guardedConstant : QueryRecovery finiteRetention (λ _ -> tt)
guardedConstant = fromQueryImageDecision {C = finiteRetention} {q = λ _ -> tt}
  (λ _ -> refl) finiteImageDecision

generatedConstantNI : ObservationNI guardedConstant (λ result -> result) (λ _ _ -> ⊤)
generatedConstantNI {x} {z} related = releaseInvariantToNI guardedConstant (λ result -> result)
  (λ _ _ -> ⊤) (λ {u} {v} _ -> refl) {x} {z} related

requestResult : Bool -> Maybe ⊤
requestResult b = QueryRecovery.answer guardedConstant (false , b) tt

reachableRequest : requestResult false ≡ just tt
reachableRequest = refl

unreachableRequest : requestResult true ≡ nothing
unreachableRequest = refl

requestStatusDifference : requestResult false ≡ requestResult true -> Impossible
requestStatusDifference ()
