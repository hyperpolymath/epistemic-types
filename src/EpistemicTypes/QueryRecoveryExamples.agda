{-# OPTIONS --safe --without-K --cubical-compatible --exact-split --no-sized-types --no-guardedness #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

module EpistemicTypes.QueryRecoveryExamples where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Maybe using (just)
open import Agda.Builtin.Sigma using (Σ; _,_; fst; snd)
open import Agda.Builtin.Unit using (⊤; tt)
open import EpistemicTypes.EchoBridge using (Retention; Impossible)
open import EpistemicTypes.PartialRecovery
  using (PartialRecovery; partialSeparates; ImageDecision; Decision; yes; no)
open import EpistemicTypes.PartialRecoveryExamples
  using (finiteRetention; finiteImageDecision; offImageIncompatible)
open import EpistemicTypes.QueryRecovery

private
  cong : {A B : Set} (f : A -> B) {x y : A} -> x ≡ y -> f x ≡ f y
  cong f refl = refl

  falseNotTrue : false ≡ true -> Impossible
  falseNotTrue ()

-- A nonconstant public query remains recoverable despite a source collision.
Pair : Set
Pair = Σ Bool (λ _ -> Bool)

publicRetention : Retention Pair Bool ⊤
Retention.observe publicRetention = fst
Retention.retain publicRetention _ = tt
Retention.Cert publicRetention _ _ = ⊤
Retention.sound publicRetention _ = tt

publicQueryConstant : QueryConstant publicRetention fst
publicQueryConstant same = cong fst same

publicImage : ImageDecision publicRetention
publicImage b tt = yes ((b , false) , refl)

publicQuery : QueryRecovery publicRetention fst
publicQuery = fromQueryImageDecision {C = publicRetention} {q = fst}
  (λ {x} {z} -> publicQueryConstant {x} {z}) publicImage

publicQuerySound : QuerySuccessSound publicQuery
publicQuerySound = queryImageDecisionSound {C = publicRetention} {q = fst}
  (λ {x} {z} -> publicQueryConstant {x} {z}) publicImage

publicQueryTrue : QueryRecovery.answer publicQuery true tt ≡ just true
publicQueryTrue = refl

noFullPublicRecovery : PartialRecovery publicRetention -> Impossible
noFullPublicRecovery rec = falseNotTrue
  (cong snd (partialSeparates rec {false , false} {false , true} refl))

-- For ANY retention a constant query can be answered with no image decision.
constantQuery : {A B R : Set} (C : Retention A B R) -> QueryRecovery C (λ _ -> tt)
QueryRecovery.answer (constantQuery C) _ _ = just tt
QueryRecovery.adequate (constantQuery C) _ = refl

constantOffImage : QueryRecovery.answer (constantQuery finiteRetention) (false , true) tt ≡ just tt
constantOffImage = refl

constantNotSuccessSound : QuerySuccessSound (constantQuery finiteRetention) -> Impossible
constantNotSuccessSound sound with sound (false , true) tt tt refl
... | b , same = falseNotTrue (cong (λ p -> snd (fst p)) same)

-- This is a constructive REDUCTION, not an assumed decision principle or
-- an undecidability theorem: unrestricted extraction would decide every P.
propositionRetention : (P : Set) -> Retention P ⊤ ⊤
Retention.observe (propositionRetention P) _ = tt
Retention.retain (propositionRetention P) _ = tt
Retention.Cert (propositionRetention P) _ _ = ⊤
Retention.sound (propositionRetention P) _ = tt

UniversalQueryImageExtraction : Set₁
UniversalQueryImageExtraction =
  {A B R T : Set} {C : Retention A B R} {q : A -> T} ->
  QueryRecovery C q -> ImageDecision C

unrestrictedExtractionDecidesEveryType : UniversalQueryImageExtraction ->
  (P : Set) -> Decision P
unrestrictedExtractionDecidesEveryType extract P
  with extract (constantQuery (propositionRetention P)) tt tt
... | yes (p , _) = yes p
... | no absent = no (λ p -> absent (p , refl))
