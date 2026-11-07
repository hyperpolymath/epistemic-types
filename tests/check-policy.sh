#!/usr/bin/env bash
# Proof-policy conformance and negative control.
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.."

required_options='{-# OPTIONS --safe --without-K --cubical-compatible --exact-split --no-sized-types --no-guardedness #-}'

# shellcheck disable=SC2034 # consumed through require_exact_inventory namerefs
expected_source_modules=(
  src/EpistemicTypes/Access.agda
  src/EpistemicTypes/All.agda
  src/EpistemicTypes/Applications/ApprovalSeal.agda
  src/EpistemicTypes/Applications/IntegerModel.agda
  src/EpistemicTypes/Applications/OrderedGroup.agda
  src/EpistemicTypes/Applications/QCriterion.agda
  src/EpistemicTypes/Applications/RapidNJExamples.agda
  src/EpistemicTypes/Applications/RapidNJSkip.agda
  src/EpistemicTypes/Applications/SortedRow.agda
  src/EpistemicTypes/Base.agda
  src/EpistemicTypes/ContinuityExamples.agda
  src/EpistemicTypes/EchoBridge.agda
  src/EpistemicTypes/Examples.agda
  src/EpistemicTypes/Kripke/Belief.agda
  src/EpistemicTypes/Kripke/Dependence.agda
  src/EpistemicTypes/Kripke/Frame.agda
  src/EpistemicTypes/Kripke/Indexed.agda
  src/EpistemicTypes/Kripke/Residual.agda
  src/EpistemicTypes/PartialRecovery.agda
  src/EpistemicTypes/PartialRecoveryExamples.agda
  src/EpistemicTypes/ProofTransport.agda
  src/EpistemicTypes/ProofTransportExample.agda
  src/EpistemicTypes/ReadConsistency.agda
  src/EpistemicTypes/SurrealBridge.agda
  src/EpistemicTypes/Warrant.agda
)
# shellcheck disable=SC2034 # consumed through require_exact_inventory namerefs
expected_rejection_fixtures=(
  tests/reject/AgentChangesAnchor.agda
  tests/reject/BeliefIsKnowledge.agda
  tests/reject/CollidingPartialRecovery.agda
  tests/reject/FakeFreshness.agda
  tests/reject/FinalStateProvesNoTouch.agda
  tests/reject/ForgedAcceptance.agda
  tests/reject/ForgedResidue.agda
  tests/reject/ForkedHistory.agda
  tests/reject/InventedMigration.agda
  tests/reject/LyingVerifier.agda
  tests/reject/MismatchedSource.agda
  tests/reject/PartialSuccessProvesImage.agda
  tests/reject/ReplayedArtifact.agda
  tests/reject/ReplayedHolder.agda
  tests/reject/ResealApprovesChange.agda
  tests/reject/RestoreErasesHistory.agda
  tests/reject/StaleSample.agda
  tests/reject/UncheckedSkip.agda
  tests/reject/UnderstatedBound.agda
)
# shellcheck disable=SC2034 # consumed through require_exact_inventory namerefs
expected_integration_modules=(
  tests/integration/CanonicalEcho.agda
  tests/integration/CanonicalPartialRecovery.agda
  tests/integration/CanonicalRecovery.agda
  tests/integration/RecoveryExamples.agda
)

collect_agda_paths() {
  local root=$1 array_name=$2 output
  local -n destination=$array_name
  destination=()
  if ! output=$(find "$root" -type f -name '*.agda' -print | LC_ALL=C sort); then
    printf 'FAIL: could not enumerate Agda files below %s\n' "$root"
    exit 1
  fi
  if [[ -n $output ]]; then
    mapfile -t destination <<< "$output"
  fi
}

require_exact_inventory() {
  local label=$1 expected_name=$2 actual_name=$3 index=0
  local -n expected=$expected_name actual=$actual_name
  if [[ ${#expected[@]} -eq ${#actual[@]} ]]; then
    for ((index = 0; index < ${#expected[@]}; index += 1)); do
      [[ ${expected[index]} == "${actual[index]}" ]] || break
    done
  fi
  if [[ ${#expected[@]} -ne ${#actual[@]} || $index -lt ${#expected[@]} ]]; then
    printf 'FAIL: %s inventory differs from its authoritative manifest\n' "$label"
    printf '%s\n' '--- expected'
    printf '%s\n' "${expected[@]}"
    printf '%s\n' '--- actual'
    printf '%s\n' "${actual[@]}"
    exit 1
  fi
}

source_modules=()
rejection_fixtures=()
integration_modules=()
collect_agda_paths src/EpistemicTypes source_modules
collect_agda_paths tests/reject rejection_fixtures
collect_agda_paths tests/integration integration_modules
require_exact_inventory 'source-module' expected_source_modules source_modules
require_exact_inventory 'rejection-fixture' expected_rejection_fixtures rejection_fixtures
require_exact_inventory 'integration-module' expected_integration_modules integration_modules

for module in "${source_modules[@]}" "${rejection_fixtures[@]}" "${integration_modules[@]}"; do
  [[ $(head -n 1 "$module") == "$required_options" ]] || {
    printf 'FAIL: %s does not declare the complete strict OPTIONS profile first\n' "$module"
    exit 1
  }

  # The required first line must be the only OPTIONS pragma. This prevents a
  # later pragma from weakening exact splitting, termination or other policy.
  options_count=0
  line_number=0
  while IFS= read -r line || [[ -n $line ]]; do
    ((line_number += 1))
    if [[ $line =~ \{\-\#[[:space:]]*OPTIONS([[:space:]]|#) ]]; then
      ((options_count += 1))
      [[ $line_number -eq 1 && $line == "$required_options" ]] || {
        printf 'FAIL: %s:%s contains an additional or non-canonical OPTIONS pragma\n' \
          "$module" "$line_number"
        exit 1
      }
    fi
  done < "$module"
  [[ $options_count -eq 1 ]] || {
    printf 'FAIL: %s must contain exactly one OPTIONS pragma, found %s\n' \
      "$module" "$options_count"
    exit 1
  }
done

# The load-bearing tree and positive integration witness must not contain proof
# escape hatches or unresolved holes. The generated negative control below is
# intentionally outside the repository tree.
if rg -n \
    -e '^[[:space:]]*postulate([[:space:]]|$)' \
    -e '\{\-#[[:space:]]*(TERMINATING|NON_TERMINATING|NO_TERMINATION_CHECK|NON_COVERING|NO_COVERAGE_CHECK|NO_POSITIVITY_CHECK|NO_UNIVERSE_CHECK|POLARITY)' \
    -e '\b(believe_me|primTrustMe|trustMe|unsafeCoerce|assert_total|Admitted|sorry)\b' \
    -e '\{!' -e '!\}' \
    src tests/integration -g '*.agda'; then
  echo 'FAIL: banned proof construct or unresolved hole found in positive proof sources'
  exit 1
else
  rg_status=$?
  [[ $rg_status -eq 1 ]] || {
    printf 'FAIL: banned proof scan failed (rg exit %s)\n' "$rg_status"
    exit 1
  }
fi

# Core source is deliberately standalone: only Agda builtins/primitive and
# modules owned by this repository may be imported. Scan lexical tokens rather
# than line starts so `module M where open import X` cannot evade the boundary;
# strip line, nested block and string contents before interpreting `import`.
check_core_imports() {
  local module=$1 line code pair char token imported
  local line_number=0 index comment_depth=0 in_string=0 escaped=0
  local expect_module=0 import_line=0
  local -a tokens=()

  [[ -r $module ]] || {
    printf 'FAIL: cannot read source while scanning imports: %s\n' "$module"
    return 1
  }

  while IFS= read -r line || [[ -n $line ]]; do
    ((line_number += 1))
    code=
    in_string=0
    escaped=0
    for ((index = 0; index < ${#line}; index += 1)); do
      char=${line:index:1}
      pair=${line:index:2}

      if ((comment_depth > 0)); then
        if [[ $pair == '{-' ]]; then
          ((comment_depth += 1))
          ((index += 1))
        elif [[ $pair == '-}' ]]; then
          comment_depth=$((comment_depth - 1))
          ((index += 1))
        fi
        continue
      fi

      if ((in_string)); then
        if ((escaped)); then
          escaped=0
        elif [[ $char == '\\' ]]; then
          escaped=1
        elif [[ $char == '"' ]]; then
          in_string=0
        fi
        code+=' '
        continue
      fi

      if [[ $pair == '--' ]]; then
        break
      elif [[ $pair == '{-' ]]; then
        ((comment_depth += 1))
        ((index += 1))
        code+=' '
      elif [[ $char == '"' ]]; then
        in_string=1
        code+=' '
      else
        case "$char" in
          ';'|'{'|'}'|'('|')') code+=' ' ;;
          *) code+=$char ;;
        esac
      fi
    done

    tokens=()
    read -r -a tokens <<< "$code"
    for token in "${tokens[@]}"; do
      if ((expect_module)); then
        imported=$token
        case "$imported" in
          Agda.Builtin.*|Agda.Primitive|EpistemicTypes.*) ;;
          *)
            printf 'FAIL: non-core import in standalone source at %s:%s: %s\n' \
              "$module" "$import_line" "$imported"
            return 1
            ;;
        esac
        expect_module=0
      elif [[ $token == import ]]; then
        expect_module=1
        import_line=$line_number
      fi
    done
  done < "$module"

  ((comment_depth == 0)) || {
    printf 'FAIL: unterminated block comment while scanning imports: %s\n' "$module"
    return 1
  }
  ((expect_module == 0)) || {
    printf 'FAIL: import without a module name at %s:%s\n' "$module" "$import_line"
    return 1
  }
}

for module in "${source_modules[@]}"; do
  check_core_imports "$module"
done

# Negative control for the checker itself. A missing tool or unrelated parser
# error is not accepted as evidence that --safe rejects postulates.
tmpdir=$(mktemp -d)
trap 'rm -rf "$tmpdir"' EXIT
cat > "$tmpdir/SafeFlagPostulate.agda" <<'AGDA'
{-# OPTIONS --safe --without-K --cubical-compatible --exact-split --no-sized-types --no-guardedness #-}
module SafeFlagPostulate where

postulate
  escape : {A : Set} → A
AGDA
status=0
diagnostic=$(agda --no-libraries --safe --without-K --cubical-compatible \
  --exact-split --no-sized-types --no-guardedness \
  --double-check --ignore-interfaces -W error -i "$tmpdir" \
  "$tmpdir/SafeFlagPostulate.agda" 2>&1) || status=$?
if [[ $status -ne 42 ]] || \
    ! rg -q '\[SafeFlagPostulate\]|Cannot postulate .*safe flag' <<< "$diagnostic"; then
  printf 'FAIL: --safe negative control failed for an unexpected reason (exit %s)\n%s\n' \
    "$status" "$diagnostic"
  exit 1
fi

printf 'PASS: exact policy manifest covers %s source modules, %s rejection fixtures and %s integration witness; --safe rejects the planted postulate\n' \
  "${#source_modules[@]}" "${#rejection_fixtures[@]}" "${#integration_modules[@]}"
