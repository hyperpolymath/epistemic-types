#!/usr/bin/env bash
# Proof-policy conformance and negative control.
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.."

required_options='{-# OPTIONS --safe --without-K --cubical-compatible --exact-split --no-sized-types --no-guardedness #-}'
mapfile -t source_modules < <(find src/EpistemicTypes -type f -name '*.agda' | sort)
mapfile -t rejection_fixtures < <(find tests/reject -type f -name '*.agda' | sort)
mapfile -t integration_modules < <(find tests/integration -type f -name '*.agda' | sort)

[[ ${#source_modules[@]} -eq 22 ]] || {
  printf 'FAIL: proof inventory drift: expected 22 source modules, found %s\n' "${#source_modules[@]}"
  exit 1
}
[[ ${#rejection_fixtures[@]} -eq 13 ]] || {
  printf 'FAIL: rejection inventory drift: expected 13 fixtures, found %s\n' "${#rejection_fixtures[@]}"
  exit 1
}
[[ ${#integration_modules[@]} -eq 1 ]] || {
  printf 'FAIL: integration inventory drift: expected 1 module, found %s\n' "${#integration_modules[@]}"
  exit 1
}

for module in "${source_modules[@]}" "${rejection_fixtures[@]}" "${integration_modules[@]}"; do
  [[ $(head -n 1 "$module") == "$required_options" ]] || {
    printf 'FAIL: %s does not declare the complete strict OPTIONS profile\n' "$module"
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
fi

# Core source is deliberately standalone: only Agda builtins/primitive and
# modules owned by this repository may occur on import lines.
while IFS= read -r import_line; do
  [[ $import_line =~ import[[:space:]]+([^[:space:]]+) ]] || {
    printf 'FAIL: could not parse import line: %s\n' "$import_line"
    exit 1
  }
  imported=${BASH_REMATCH[1]}
  case "$imported" in
    Agda.Builtin.*|Agda.Primitive|EpistemicTypes.*) ;;
    *) printf 'FAIL: non-core import in standalone source: %s\n' "$import_line"; exit 1 ;;
  esac
done < <(rg -N --no-filename '^[[:space:]]*(open[[:space:]]+)?import[[:space:]]+' src/EpistemicTypes -g '*.agda')

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
  --double-check --ignore-interfaces -W error -i "$tmpdir" \
  "$tmpdir/SafeFlagPostulate.agda" 2>&1) || status=$?
if [[ "$status" -ne 42 ]] || \
    ! rg -q '\[SafeFlagPostulate\]|Cannot postulate .*safe flag' <<< "$diagnostic"; then
  printf 'FAIL: --safe negative control failed for an unexpected reason (exit %s)\n%s\n' \
    "$status" "$diagnostic"
  exit 1
fi

printf 'PASS: policy profile covers %s source modules, %s rejection fixtures and %s integration witness; --safe rejects the planted postulate\n' \
  "${#source_modules[@]}" "${#rejection_fixtures[@]}" "${#integration_modules[@]}"
