#!/usr/bin/env bash
# Deterministic theorem-sensitivity controls, isolated from the real source tree.
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.."
source_file=src/EpistemicTypes/Applications/ApprovalSeal.agda
flags=(--no-libraries --safe --without-K --cubical-compatible --exact-split
  --no-sized-types --no-guardedness --double-check --ignore-interfaces -W error)

# A missing checker or universally rejecting checker must fail the positive leg.
timeout 20s agda "${flags[@]}" -i src "$source_file"
tmpdir=$(mktemp -d)
trap 'rm -rf "$tmpdir"' EXIT

mutate() {
  local name=$1 original=$2 replacement=$3 expected=$4 status=0 diagnostic
  local root="$tmpdir/$name"
  local target="$root/EpistemicTypes/Applications/ApprovalSeal.agda"
  mkdir -p -- "$(dirname -- "$target")"
  # Refuse to run a stale mutation against zero or several matching lines.
  awk -v old="$original" -v new="$replacement" '
    $0 == old { print new; replacements++; next }
    { print }
    END { if (replacements != 1) exit 1 }
  ' "$source_file" > "$target"

  # Only isolated invalid mutants suppress the transport warning so they reach
  # their semantic error. The unchanged positive module has no suppression.
  diagnostic=$(timeout 20s agda "${flags[@]}" -W noUnsupportedIndexedMatch \
    -i "$root" "$target" 2>&1) || status=$?
  if [[ $status -ne 42 ]] || ! rg -q -- "$expected" <<< "$diagnostic" || \
      ! rg -q 'when checking' <<< "$diagnostic"; then
    printf 'FAIL: %s did not produce the required semantic rejection (exit %s)\n%s\n' \
      "$name" "$status" "$diagnostic"
    exit 1
  fi
  printf 'PASS: %s rejected with Agda exit 42 and its expected semantic diagnostic\n' "$name"
}

mutate always-accept \
  'gate (state _ _ _ true) = sealBroken' \
  'gate (state _ _ _ true) = accepted' \
  'should be empty, but the following constructor patterns are valid'
mutate local-root-replacement \
  'step (writeLocalReference x) s = state (anchor s) (artifact s) x (broken s)' \
  'step (writeLocalReference x) s = state x (artifact s) x (broken s)' \
  'x != anchor s'
mutate write-without-latch \
  'step (writeArtifact x) s = state (anchor s) x (localReference s) true' \
  'step (writeArtifact x) s = state (anchor s) x (localReference s) (broken s)' \
  'broken s != true'
mutate clear-on-reseal \
  'step (writeLocalReference x) s = state (anchor s) (artifact s) x (broken s)' \
  'step (writeLocalReference x) s = state (anchor s) (artifact s) x false' \
  'broken s != false'
printf 'PASS: 4/4 fixed approval-seal mutants rejected; 20-second bound per invocation\n'
