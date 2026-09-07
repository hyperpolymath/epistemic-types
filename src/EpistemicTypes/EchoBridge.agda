{-# OPTIONS --safe --without-K #-}

module EpistemicTypes.EchoBridge where

open import Agda.Primitive using (lzero)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import EpistemicTypes.Base

-- The certification shape follows canonical EchoResidue.EchoR. This small
-- interface uses builtins only; cross-repository correspondence is checked
-- separately. Cert is supplied by the consumer, so its intended meaning must
-- be reviewed. No recovery or information-loss bound follows from its name.
record Retention (Source Visible Residue : Set) : Set₁ where
  field
    observe : Source -> Visible
    retain  : Source -> Residue
    Cert    : Residue -> Visible -> Set
    sound   : (x : Source) -> Cert (retain x) (observe x)

record Echo {A B R : Set} (C : Retention A B R) (y : B) : Set where
  constructor echo
  field
    residue   : R
    certified : Retention.Cert C residue y

lower : {A B R : Set} (C : Retention A B R) (x : A) ->
  Echo C (Retention.observe C x)
lower C x = echo (Retention.retain C x) (Retention.sound C x)

-- A candidate source must match both the observation and residue. This is
-- compatibility, not proof of historical origin: multiple sources can match
-- after information loss. Actual execution provenance needs another model.
record MatchesSource {A B R : Set} (C : Retention A B R) (x : A)
  {y : B} (e : Echo C y) : Set where
  constructor matchesSource
  field
    observationMatches : Retention.observe C x ≡ y
    residueMatches : Retention.retain C x ≡ Echo.residue e

lowerMatchesSource : {A B R : Set} (C : Retention A B R) (x : A) -> MatchesSource C x (lower C x)
lowerMatchesSource C x = matchesSource refl refl

-- Recovering a source requires a left-inverse law for the ACTUAL observation
-- and residue functions. A certificate alone need not supply this capability.
record Recovery {A B R : Set} (C : Retention A B R) : Set where
  field
    recover   : B -> R -> A
    roundtrip : (x : A) -> recover (Retention.observe C x) (Retention.retain C x) ≡ x

recoverLower : {A B R : Set} {C : Retention A B R} (rec : Recovery C) (x : A) ->
  Recovery.recover rec (Retention.observe C x) (Echo.residue (lower C x)) ≡ x
recoverLower rec x = Recovery.roundtrip rec x

recoverMatching : {A B R : Set} {C : Retention A B R} (rec : Recovery C)
  (x : A) {y : B} (e : Echo C y) -> MatchesSource C x e ->
  Recovery.recover rec y (Echo.residue e) ≡ x
recoverMatching rec x e (matchesSource refl refl) = Recovery.roundtrip rec x

-- A migration can need less information than full source recovery. Its
-- implementation must factor the specified target behaviour through the
-- actual retained pair. This is the load-bearing sufficiency obligation.
record Migration {A B R T : Set} (C : Retention A B R) (target : A -> T) : Set where
  field
    migrate  : B -> R -> T
    adequate : (x : A) -> migrate (Retention.observe C x) (Retention.retain C x) ≡ target x

migrateLower : {A B R T : Set} {C : Retention A B R} {target : A -> T} ->
  (m : Migration C target) (x : A) ->
  Migration.migrate m (Retention.observe C x) (Echo.residue (lower C x)) ≡ target x
migrateLower m x = Migration.adequate m x

migrateMatching : {A B R T : Set} {C : Retention A B R} {target : A -> T}
  (m : Migration C target) (x : A) {y : B} (e : Echo C y) -> MatchesSource C x e ->
  Migration.migrate m y (Echo.residue e) ≡ target x
migrateMatching m x e (matchesSource refl refl) = Migration.adequate m x

data Impossible : Set where

private
  sym : {A : Set} {x y : A} -> x ≡ y -> y ≡ x
  sym refl = refl

  trans : {A : Set} {x y z : A} -> x ≡ y -> y ≡ z -> x ≡ z
  trans refl q = q

  cong₂ : {A B T : Set} (f : A -> B -> T) {a a' : A} {b b' : B} ->
    a ≡ a' -> b ≡ b' -> f a b ≡ f a' b'
  cong₂ f refl refl = refl

-- Equal retained observations cannot support differing required results.
-- This rules out ALL migrations with this signature, not just one candidate.
collisionForbidsMigration : {A B R T : Set} (C : Retention A B R)
  (target : A -> T) (x x' : A) ->
  Retention.observe C x ≡ Retention.observe C x' ->
  Retention.retain C x ≡ Retention.retain C x' ->
  (target x ≡ target x' -> Impossible) -> Migration C target -> Impossible
collisionForbidsMigration C target x x' sameVisible sameResidue distinct m =
  distinct (trans (sym (Migration.adequate m x))
    (trans (cong₂ (Migration.migrate m) sameVisible sameResidue)
      (Migration.adequate m x')))

-- Changing the observation/residue contract requires certificate transport.
-- This proves preservation of Cert, not an unstated source-recovery law.
record EchoMap {A B R A' B' R' : Set}
  (C : Retention A B R) (D : Retention A' B' R') : Set where
  field
    mapVisible : B -> B'
    mapResidue : R -> R'
    preserves  : {r : R} {y : B} -> Retention.Cert C r y ->
      Retention.Cert D (mapResidue r) (mapVisible y)

mapEcho : {A B R A' B' R' : Set}
  {C : Retention A B R} {D : Retention A' B' R'} ->
  (m : EchoMap C D) {y : B} -> Echo C y -> Echo D (EchoMap.mapVisible m y)
mapEcho m (echo r cert) = echo (EchoMap.mapResidue m r) (EchoMap.preserves m cert)

EpistemicEcho : {K A B R : Set} -> Modality K lzero ->
  K -> (C : Retention A B R) -> B -> Set
EpistemicEcho M κ C y = Modality.E M κ (Echo C y)

-- Resource bounds are a separate axis. These are upper bounds on a supplied
-- residue measure; they are not Echo retention indices or physical timings.
data Grade : Set where
  finite   : Nat -> Grade
  infinity : Grade

minNat : Nat -> Nat -> Nat
minNat zero n = zero
minNat (suc m) zero = zero
minNat (suc m) (suc n) = suc (minNat m n)

gradeMin : Grade -> Grade -> Grade
gradeMin (finite m) (finite n) = finite (minNat m n)
gradeMin (finite m) infinity = finite m
gradeMin infinity (finite n) = finite n
gradeMin infinity infinity = infinity

gradePlus : Grade -> Grade -> Grade
gradePlus (finite m) (finite n) = finite (m + n)
gradePlus (finite m) infinity = infinity
gradePlus infinity (finite n) = infinity
gradePlus infinity infinity = infinity

data _≤ℕ_ : Nat -> Nat -> Set where
  zero≤ : {n : Nat} -> zero ≤ℕ n
  suc≤  : {m n : Nat} -> m ≤ℕ n -> suc m ≤ℕ suc n

≤ℕ-trans : {a b c : Nat} -> a ≤ℕ b -> b ≤ℕ c -> a ≤ℕ c
≤ℕ-trans zero≤ _ = zero≤
≤ℕ-trans (suc≤ p) (suc≤ q) = suc≤ (≤ℕ-trans p q)

≤ℕ-plus : (a b : Nat) -> a ≤ℕ (a + b)
≤ℕ-plus zero b = zero≤
≤ℕ-plus (suc a) b = suc≤ (≤ℕ-plus a b)

data _≤G_ : Grade -> Grade -> Set where
  finite≤ : {m n : Nat} -> m ≤ℕ n -> finite m ≤G finite n
  top≤    : {g : Grade} -> g ≤G infinity

≤G-trans : {a b c : Grade} -> a ≤G b -> b ≤G c -> a ≤G c
≤G-trans (finite≤ p) (finite≤ q) = finite≤ (≤ℕ-trans p q)
≤G-trans p top≤ = top≤

≤G-plus : (a b : Grade) -> a ≤G gradePlus a b
≤G-plus (finite a) (finite b) = finite≤ (≤ℕ-plus a b)
≤G-plus (finite _) infinity = top≤
≤G-plus infinity (finite _) = top≤
≤G-plus infinity infinity = top≤

record BoundedEcho {A B R : Set} (C : Retention A B R)
  (measure : R -> Grade) (budget : Grade) (y : B) : Set where
  constructor bounded
  field
    retained : Echo C y
    within   : measure (Echo.residue retained) ≤G budget

weakenBound : {A B R : Set} {C : Retention A B R} {measure : R -> Grade}
  {r r' : Grade} {y : B} -> r ≤G r' ->
  BoundedEcho C measure r y -> BoundedEcho C measure r' y
weakenBound p (bounded e bound) = bounded e (≤G-trans bound p)

weakenPreservesResidue : {A B R : Set} {C : Retention A B R}
  {measure : R -> Grade} {r r' : Grade} {y : B} ->
  (p : r ≤G r') (e : BoundedEcho C measure r y) ->
  Echo.residue (BoundedEcho.retained (weakenBound p e)) ≡
  Echo.residue (BoundedEcho.retained e)
weakenPreservesResidue p e = refl
