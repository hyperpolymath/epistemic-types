{-# OPTIONS --safe --without-K --cubical-compatible --exact-split --no-sized-types --no-guardedness #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

module EpistemicTypes.ResidueSufficiency where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Unit using (⊤; tt)
open import EpistemicTypes.EchoBridge using (Retention; Migration)

private
  trans : {A : Set} {x y z : A} -> x ≡ y -> y ≡ z -> x ≡ z
  trans refl p = p

  cong : {A B : Set} (f : A -> B) {x y : A} -> x ≡ y -> f x ≡ f y
  cong f refl = refl

-- r is no more informative than s RELATIVE TO the already visible f.
-- A total simulator is explicit; its law is only on generated inputs.
-- This is a semantic preorder, with no byte/cost/uniqueness assertion.
record RelativeReduction {A B R S : Set} (f : A -> B)
  (r : A -> R) (s : A -> S) : Set where
  field
    reduce : B -> S -> R
    realizes : (x : A) -> reduce (f x) (s x) ≡ r x

relativeRefl : {A B R : Set} {f : A -> B} {r : A -> R} -> RelativeReduction f r r
RelativeReduction.reduce relativeRefl _ v = v
RelativeReduction.realizes relativeRefl _ = refl

relativeTrans : {A B R S T : Set} {f : A -> B} {r : A -> R} {s : A -> S} {t : A -> T} ->
  RelativeReduction f r s -> RelativeReduction f s t -> RelativeReduction f r t
RelativeReduction.reduce (relativeTrans rs st) b v =
  RelativeReduction.reduce rs b (RelativeReduction.reduce st b v)
RelativeReduction.realizes (relativeTrans {f = f} rs st) x =
  trans (cong (RelativeReduction.reduce rs (f x)) (RelativeReduction.realizes st x))
    (RelativeReduction.realizes rs x)

-- This creates an observation/retention contract with a trivial certificate.
-- It does not transport an old Cert or confer any authentication guarantee.
replaceResidue : {A B R S : Set} -> Retention A B R -> (A -> S) -> Retention A B S
Retention.observe (replaceResidue C s) = Retention.observe C
Retention.retain (replaceResidue C s) = s
Retention.Cert (replaceResidue C s) _ _ = ⊤
Retention.sound (replaceResidue C s) _ = tt

queryResidueAdequate : {A B R T : Set} (C : Retention A B R) (q : A -> T) ->
  Migration (replaceResidue C q) q
Migration.migrate (queryResidueAdequate C q) _ t = t
Migration.adequate (queryResidueAdequate C q) _ = refl

-- The query residue itself is least among residues sufficient for this
-- total Migration contract. This packages factorization, not compression.
queryResidueLeast : {A B R T : Set} {C : Retention A B R} {q : A -> T} ->
  Migration C q -> RelativeReduction (Retention.observe C) q (Retention.retain C)
RelativeReduction.reduce (queryResidueLeast m) = Migration.migrate m
RelativeReduction.realizes (queryResidueLeast m) = Migration.adequate m

reductionToMigration : {A B R T : Set} {C : Retention A B R} {q : A -> T} ->
  RelativeReduction (Retention.observe C) q (Retention.retain C) -> Migration C q
Migration.migrate (reductionToMigration r) = RelativeReduction.reduce r
Migration.adequate (reductionToMigration r) = RelativeReduction.realizes r

-- Strengthening available residue preserves any already adequate query.
migrateWithMoreResidue : {A B R S T : Set} {C : Retention A B R} {q : A -> T}
  (s : A -> S) -> RelativeReduction (Retention.observe C) (Retention.retain C) s ->
  Migration C q -> Migration (replaceResidue C s) q
Migration.migrate (migrateWithMoreResidue s reduction m) b v =
  Migration.migrate m b (RelativeReduction.reduce reduction b v)
Migration.adequate (migrateWithMoreResidue {C = C} s reduction m) x =
  trans (cong (Migration.migrate m (Retention.observe C x)) (RelativeReduction.realizes reduction x))
    (Migration.adequate m x)
