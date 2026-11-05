#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.."

# Each fixture must reach its intended type error. Missing tools/imports or
# unrelated parse failures must fail this gate rather than count as rejection.
fixtures=(LyingVerifier ForgedAcceptance ReplayedArtifact ReplayedHolder \
  StaleSample FakeFreshness ForkedHistory ForgedResidue MismatchedSource \
  UnderstatedBound InventedMigration UncheckedSkip BeliefIsKnowledge \
  AgentChangesAnchor FinalStateProvesNoTouch ResealApprovesChange RestoreErasesHistory)
expected_files=$(printf 'tests/reject/%s.agda\n' "${fixtures[@]}" | sort)
actual_files=$(rg --files tests/reject -g '*.agda' | sort)
[[ "$actual_files" == "$expected_files" ]] || { echo 'FAIL: rejection manifest differs from files'; exit 1; }
for fixture in "${fixtures[@]}"; do
  status=0
  # Source warning locations are audited by check-proofs.sh; this suppression
  # only lets each negative fixture reach the exact mismatch asserted below.
  diagnostic=$(agda --no-libraries --safe --without-K --cubical-compatible \
    --exact-split --no-sized-types --no-guardedness \
    --double-check --ignore-interfaces \
    -W error -W noUnsupportedIndexedMatch -i src -i tests/reject \
    "tests/reject/$fixture.agda" 2>&1) || status=$?
  if [[ "$status" -eq 0 ]]; then
    printf 'FAIL: %s unexpectedly type-checked\n' "$fixture"
    exit 1
  fi
  case "$fixture" in
    LyingVerifier|ForgedAcceptance) expected='false != .*true' ;;
    ReplayedArtifact) expected='true != .*false' ;;
    ReplayedHolder) expected='Alice != .*Bob' ;;
    StaleSample|ForkedHistory|ForgedResidue|MismatchedSource) expected='false != .*true' ;;
    UncheckedSkip) expected='false != .*true' ;;
    FakeFreshness) expected='initial .*false !=' ;;
    UnderstatedBound) expected='1 != 0' ;;
    InventedMigration) expected='true != .*false' ;;
    BeliefIsKnowledge) expected='w₁ != .*w₀' ;;
    AgentChangesAnchor) expected='0 != 1' ;;
    FinalStateProvesNoTouch) expected='true != .*false' ;;
    ResealApprovesChange|RestoreErasesHistory) expected='sealBroken != .*accepted' ;;
  esac
  if [[ "$status" -ne 42 ]] || ! rg -q "$expected" <<< "$diagnostic" || \
      ! rg -q 'when checking' <<< "$diagnostic"; then
    printf 'FAIL: %s failed for an unexpected reason\n%s\n' "$fixture" "$diagnostic"
    exit 1
  fi
  printf 'PASS: %s rejected for the expected type mismatch\n' "$fixture"
done
