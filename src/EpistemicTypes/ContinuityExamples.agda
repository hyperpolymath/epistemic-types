{-# OPTIONS --safe --without-K #-}

module EpistemicTypes.ContinuityExamples where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (zero; suc)
open import Agda.Builtin.Sigma using (Σ; _,_; fst; snd)
open import Agda.Builtin.Unit using (⊤; tt)
import EpistemicTypes.ReadConsistency as Read
import EpistemicTypes.EchoBridge as Echo
import EpistemicTypes.SurrealBridge as Surreal

module Reads where
  open Read

  before : Store Bool
  before = initial false

  after : Store Bool
  after = write before true

  anotherWrite : Store Bool
  anotherWrite = write after false

  old : CachedRead before
  old = synchronize before

  historical : CachedRead after
  historical = advanceCache true old

  oldSamplePreserved : cachedValue historical ≡ false
  oldSamplePreserved = refl

  oldSampleNotFresh : ¬ (Fresh historical)
  oldSampleNotFresh = writeInvalidatesFreshness true old

  refreshActuallyChangesValue : cachedValue (synchronize after) ≡ true
  refreshActuallyChangesValue = syncReadsCurrent after

  refreshAfterTwoWrites : Fresh (synchronize anotherWrite)
  refreshAfterTwoWrites = syncRestoresFresh anotherWrite

  historicalAgain : CachedRead anotherWrite
  historicalAgain = advanceCache false historical

  valueReturnedButSnapshotDidNot : cachedValue historicalAgain ≡ contents anotherWrite
  valueReturnedButSnapshotDidNot = refl

  stillHistoricalAfterValueReturns : ¬ (Fresh historicalAgain)
  stillHistoricalAfterValueReturns = writeInvalidatesFreshness false historical

  falseIsNotTrue : false ≡ true -> ⊥
  falseIsNotTrue ()

  cannotKeepFalseAsCurrent : (rv : ReadView after) -> value rv ≡ false -> ⊥
  cannotKeepFalseAsCurrent (readView .false eq) refl = falseIsNotTrue eq

  -- Version equality alone does not identify a store or its contents.
  otherBranch : Store Bool
  otherBranch = write before false

  sameVersion : version after ≡ version otherBranch
  sameVersion = refl

  differentCurrentValues : contents otherBranch ≡ contents after -> ⊥
  differentCurrentValues = falseIsNotTrue

  -- The sample is still historical after a value-preserving write, but an
  -- explicit value equality allows it to become a certified current view.
  sameValue : Store Bool
  sameValue = write before false

  retainedValue : ReadView sameValue
  retainedValue = retainUnchanged (earlier here) refl (readCurrent before)

  retainedValueIsFalse : value retainedValue ≡ false
  retainedValueIsFalse = refl

  -- A fact about one component can survive a change to another component.
  Pair : Set
  Pair = Σ Bool (λ _ -> Bool)

  pairBefore : Store Pair
  pairBefore = initial (true , false)

  pairAfter : Store Pair
  pairAfter = write pairBefore (true , true)

  FirstIsTrue : Pair -> Set
  FirstIsTrue pair = fst pair ≡ true

  unaffectedFact : FactAt pairAfter FirstIsTrue
  unaffectedFact = transportFact {s = pairBefore} {t = pairAfter}
    {P = FirstIsTrue} (λ p -> p) refl

  -- There is no value-preserving version-only transport for arbitrary writes.
  noUniversalValueRetag :
    ((s : Store Bool) (a : Bool) (rv : ReadView s) ->
      Σ (ReadView (write s a)) (λ next -> value next ≡ value rv)) -> ⊥
  noUniversalValueRetag retag with retag before true (readCurrent before)
  ... | next , unchanged = cannotKeepFalseAsCurrent next unchanged

module Residues where
  open Echo

  -- Identity observation and retention give valid and invalid certificates
  -- for the same contract: the residue must equal the indexed visible value.
  identityRetention : Retention Bool Bool Bool
  Retention.observe identityRetention b = b
  Retention.retain identityRetention b = b
  Retention.Cert identityRetention r y = r ≡ y
  Retention.sound identityRetention b = refl

  identityTrue : Echo identityRetention true
  identityTrue = lower identityRetention true

  identityRecovery : Recovery identityRetention
  Recovery.recover identityRecovery _ r = r
  Recovery.roundtrip identityRecovery b = refl

  trueRoundtrip : Recovery.recover identityRecovery true
    (Echo.residue identityTrue) ≡ true
  trueRoundtrip = recoverLower identityRecovery true

  -- Forget the second Boolean while retaining exactly the first. The target
  -- needs only the first, so its migration is adequate despite lost data.
  Pair : Set
  Pair = Σ Bool (λ _ -> Bool)

  firstRetention : Retention Pair ⊤ Bool
  Retention.observe firstRetention _ = tt
  Retention.retain firstRetention pair = fst pair
  Retention.Cert firstRetention _ _ = ⊤
  Retention.sound firstRetention _ = tt

  -- Compatibility does not identify the original source after loss: this
  -- echo was lowered from (true,false) and also matches (true,true).
  ambiguousSource : MatchesSource firstRetention (true , true)
    (lower firstRetention (true , false))
  ambiguousSource = matchesSource refl refl

  firstMigration : Migration firstRetention fst
  Migration.migrate firstMigration _ r = r
  Migration.adequate firstMigration pair = refl

  migrateFirst : Migration.migrate firstMigration tt
    (Echo.residue (lower firstRetention (true , false))) ≡ true
  migrateFirst = migrateMatching firstMigration (true , false)
    (lower firstRetention (true , false)) (lowerMatchesSource firstRetention (true , false))

  falseIsNotTrue : false ≡ true -> Impossible
  falseIsNotTrue ()

  -- Both source states have exactly the same visible value and residue.
  -- Consequently NO implementation can migrate the discarded second bit.
  cannotMigrateSecond : Migration firstRetention snd -> Impossible
  cannotMigrateSecond = collisionForbidsMigration firstRetention snd
    (true , false) (true , true) refl refl falseIsNotTrue

  constantCost : Bool -> Grade
  constantCost _ = finite (suc zero)

  boundedTrue : BoundedEcho identityRetention constantCost (finite (suc zero)) true
  boundedTrue = bounded identityTrue (finite≤ (suc≤ zero≤))

  relaxed : BoundedEcho identityRetention constantCost (finite (suc (suc zero))) true
  relaxed = weakenBound (finite≤ (suc≤ zero≤)) boundedTrue

  boundRelaxationPreservesData : Echo.residue (BoundedEcho.retained relaxed) ≡ true
  boundRelaxationPreservesData = refl

  oneDoesNotFitZero : finite (suc zero) ≤G finite zero -> Impossible
  oneDoesNotFitZero (finite≤ ())

  noUnderstatedBound : BoundedEcho identityRetention constantCost (finite zero) true -> Impossible
  noUnderstatedBound e = oneDoesNotFitZero (BoundedEcho.within e)

  -- Concrete use of the repaired surreal adapter: day access relaxes a proved
  -- bound from one to three, and the certified data remains true.
  dayTransport : BoundedEcho identityRetention constantCost
    (finite (suc (suc (suc zero)))) true
  dayTransport = Surreal.GradedSurrealModality.transportWithLoss
    (Surreal.surrealEchoKnowledge Surreal.daySurrealAccess)
    (Surreal.z≤n {n = suc (suc zero)}) (finite (suc zero)) boundedTrue

  dayTransportPreservesData : Echo.residue (BoundedEcho.retained dayTransport) ≡ true
  dayTransportPreservesData = refl
