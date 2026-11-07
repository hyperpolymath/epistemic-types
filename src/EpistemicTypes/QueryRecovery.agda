{-# OPTIONS --safe --without-K --cubical-compatible --exact-split --no-sized-types --no-guardedness #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

module EpistemicTypes.QueryRecovery where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Maybe using (Maybe; just; nothing)
open import Agda.Builtin.Sigma using (Σ; _,_; fst; snd)
open import EpistemicTypes.EchoBridge using (Retention; Migration; Impossible)
open import EpistemicTypes.PartialRecovery
  using (PartialRecovery; Image; ImageDecision; Decision; yes; no; retainedPair; withDefault)

private
  sym : {A : Set} {x y : A} -> x ≡ y -> y ≡ x
  sym refl = refl

  trans : {A : Set} {x y z : A} -> x ≡ y -> y ≡ z -> x ≡ z
  trans refl p = p

  cong : {A B : Set} (f : A -> B) {x y : A} -> x ≡ y -> f x ≡ f y
  cong f refl = refl

  justInjective : {A : Set} {x y : A} -> just x ≡ just y -> x ≡ y
  justInjective {x = x} = cong (withDefault x)

  nothingNotJust : {A : Set} {x : A} -> nothing ≡ just x -> Impossible
  nothingNotJust ()

  eliminate : {A : Set} -> Impossible -> A
  eliminate ()

mapMaybe : {A T : Set} -> (A -> T) -> Maybe A -> Maybe T
mapMaybe q nothing = nothing
mapMaybe q (just x) = just (q x)

-- The answer consumes ONLY a visible/residue pair, never a Case or source
-- witness. Correctness constrains generated inputs; off-image behaviour is
-- deliberately separate. The target may forget distinctions in the source.
record QueryRecovery {A B R T : Set} (C : Retention A B R) (q : A -> T) : Set where
  field
    answer : B -> R -> Maybe T
    adequate : (x : A) ->
      answer (Retention.observe C x) (Retention.retain C x) ≡ just (q x)

QueryConstant : {A B R T : Set} -> Retention A B R -> (A -> T) -> Set
QueryConstant C q = ∀ {x z} -> retainedPair C x ≡ retainedPair C z -> q x ≡ q z

queryConstant : {A B R T : Set} {C : Retention A B R} {q : A -> T} ->
  QueryRecovery C q -> QueryConstant C q
queryConstant rec {x} {z} same = justInjective
  (trans (sym (QueryRecovery.adequate rec x))
    (trans (cong (λ pair -> QueryRecovery.answer rec (fst pair) (snd pair)) same)
      (QueryRecovery.adequate rec z)))

queryComplete : {A B R T : Set} {C : Retention A B R} {q : A -> T}
  (rec : QueryRecovery C q) {y : B} {r : R} (w : Image C y r) ->
  QueryRecovery.answer rec y r ≡ just (q (fst w))
queryComplete rec (x , same) =
  trans (sym (cong (λ p -> QueryRecovery.answer rec (fst p) (snd p)) same))
    (QueryRecovery.adequate rec x)

sourceToQuery : {A B R T : Set} {C : Retention A B R} (q : A -> T) ->
  PartialRecovery C -> QueryRecovery C q
QueryRecovery.answer (sourceToQuery q rec) y r = mapMaybe q (PartialRecovery.decode rec y r)
QueryRecovery.adequate (sourceToQuery q rec) x =
  cong (mapMaybe q) (PartialRecovery.roundtrip rec x)

identityQueryToSource : {A B R : Set} {C : Retention A B R} ->
  QueryRecovery C (λ x -> x) -> PartialRecovery C
PartialRecovery.decode (identityQueryToSource rec) = QueryRecovery.answer rec
PartialRecovery.roundtrip (identityQueryToSource rec) = QueryRecovery.adequate rec

migrationToQuery : {A B R T : Set} {C : Retention A B R} {q : A -> T} ->
  Migration C q -> QueryRecovery C q
QueryRecovery.answer (migrationToQuery m) y r = just (Migration.migrate m y r)
QueryRecovery.adequate (migrationToQuery m) x = cong just (Migration.adequate m x)

-- This fallback is explicit target data, not a source witness or choice axiom.
queryToMigration : {A B R T : Set} {C : Retention A B R} {q : A -> T} ->
  T -> QueryRecovery C q -> Migration C q
Migration.migrate (queryToMigration fallback rec) y r =
  withDefault fallback (QueryRecovery.answer rec y r)
Migration.adequate (queryToMigration fallback rec) x =
  cong (withDefault fallback) (QueryRecovery.adequate rec x)

-- Agreement with ANY supplied source witness follows from adequacy alone.
successfulQueryAgrees : {A B R T : Set} {C : Retention A B R} {q : A -> T}
  (rec : QueryRecovery C q) {y : B} {r : R} {t : T} ->
  QueryRecovery.answer rec y r ≡ just t -> (w : Image C y r) -> q (fst w) ≡ t
successfulQueryAgrees rec success w =
  justInjective (trans (sym (queryComplete rec w)) success)

-- The additional success obligation is precisely an actual image witness.
-- No query-equality field is needed: successfulQueryAgrees derives it.
-- Agreement with sources IF any exist does not justify the converse.
QuerySuccessSound : {A B R T : Set} {C : Retention A B R} {q : A -> T} ->
  QueryRecovery C q -> Set
QuerySuccessSound {B = B} {R = R} {T = T} {C = C} {q = q} rec =
  (y : B) (r : R) (t : T) -> QueryRecovery.answer rec y r ≡ just t -> Image C y r

soundQueryDecidesImage : {A B R T : Set} {C : Retention A B R} {q : A -> T}
  (rec : QueryRecovery C q) -> QuerySuccessSound rec -> ImageDecision C
soundQueryDecidesImage rec sound y r with QueryRecovery.answer rec y r in result
... | just t = yes (sound y r t result)
... | nothing = no (λ w -> nothingNotJust (trans (sym result) (queryComplete rec w)))

private
  queryValue : {A B R T : Set} {C : Retention A B R} (q : A -> T) {y : B} {r : R} ->
    Decision (Image C y r) -> Maybe T
  queryValue q (yes (x , _)) = just (q x)
  queryValue q (no _) = nothing

fromQueryImageDecision : {A B R T : Set} {C : Retention A B R} {q : A -> T} ->
  QueryConstant C q -> ImageDecision C -> QueryRecovery C q
QueryRecovery.answer (fromQueryImageDecision {C = C} {q = q} constant decide) y r =
  queryValue {C = C} q (decide y r)
QueryRecovery.adequate (fromQueryImageDecision {C = C} constant decide) x
  with decide (Retention.observe C x) (Retention.retain C x)
... | yes (z , same) = cong just (constant same)
... | no absent = eliminate (absent (x , refl))

queryImageDecisionSound : {A B R T : Set} {C : Retention A B R} {q : A -> T}
  (constant : QueryConstant C q) (decide : ImageDecision C) ->
  QuerySuccessSound (fromQueryImageDecision {C = C} {q = q} constant decide)
queryImageDecisionSound constant decide y r t success with decide y r
... | yes (x , same) = x , same
... | no absent = eliminate (nothingNotJust success)
