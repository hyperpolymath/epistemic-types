#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.."

# Check each source module, including any new module omitted from All.agda.
# The search is recursive so that modules in subdirectories (for example the
# Applications/ tree) are gated even when they are not re-exported by All.agda.
mapfile -t modules < <(find src/EpistemicTypes -name '*.agda' | sort)
[[ ${#modules[@]} -gt 0 ]] || { echo 'FAIL: no proof modules'; exit 1; }

agda_flags=(
  --no-libraries
  --safe
  --without-K
  --cubical-compatible
  --exact-split
  --no-sized-types
  --no-guardedness
  --double-check
  --ignore-interfaces
  -i src
)

# Agda 2.6.4.3 reports cubical transport-computation limitations for these
# existing indexed eliminations. The category-level suppression in the strict
# pass is paired with a second pass that must reproduce this exact location
# manifest: a warning at any new span fails the gate, as does a stale entry.
allowed_unsupported_locations=(
  src/EpistemicTypes/Applications/IntegerModel.agda:80,1-21
  src/EpistemicTypes/Applications/IntegerModel.agda:89,1-90,66
  src/EpistemicTypes/Applications/IntegerModel.agda:236,22-43
  src/EpistemicTypes/Applications/SortedRow.agda:58,3-59,54
  src/EpistemicTypes/Applications/SortedRow.agda:78,3-82,24
  src/EpistemicTypes/ContinuityExamples.agda:174,3-33
  src/EpistemicTypes/EchoBridge.agda:156,1-157,49
  src/EpistemicTypes/EchoBridge.agda:168,1-169,58
  src/EpistemicTypes/Examples.agda:36,1-40,33
  src/EpistemicTypes/Kripke/Belief.agda:32,1-23
  src/EpistemicTypes/Kripke/Dependence.agda:76,1-77,67
  src/EpistemicTypes/Kripke/Residual.agda:61,1-62,33
  src/EpistemicTypes/ProofTransport.agda:108,1-111,91
  src/EpistemicTypes/ProofTransport.agda:130,1-82
  src/EpistemicTypes/ProofTransport.agda:187,1-189,59
  src/EpistemicTypes/ProofTransport.agda:201,1-49
  src/EpistemicTypes/ProofTransport.agda:224,1-81
  src/EpistemicTypes/ProofTransport.agda:231,1-85
  src/EpistemicTypes/ReadConsistency.agda:51,1-52,44
  src/EpistemicTypes/ReadConsistency.agda:62,1-38
  src/EpistemicTypes/SurrealBridge.agda:212,1-213,44
  src/EpistemicTypes/SurrealBridge.agda:216,1-217,42
  src/EpistemicTypes/SurrealBridge.agda:232,1-233,48
)
declare -A allowed_unsupported=()
declare -A observed_unsupported=()
for location in "${allowed_unsupported_locations[@]}"; do
  allowed_unsupported["$location"]=1
done

# All warning categories except the location-audited category remain errors.
for module in "${modules[@]}"; do
  agda "${agda_flags[@]}" -W error -W noUnsupportedIndexedMatch "$module"
done

for module in "${modules[@]}"; do
  status=0
  diagnostic=$(agda "${agda_flags[@]}" -W noerror "$module" 2>&1) || status=$?
  [[ $status -eq 0 ]] || {
    printf 'FAIL: warning audit could not check %s (Agda exit %s)\n%s\n' \
      "$module" "$status" "$diagnostic"
    exit 1
  }

  previous_line=
  while IFS= read -r diagnostic_line; do
    if [[ $diagnostic_line == 'warning: -W[no]UnsupportedIndexedMatch' ]]; then
      location=${previous_line#"$PWD/"}
      [[ -n ${allowed_unsupported["$location"]+present} ]] || {
        printf 'FAIL: UnsupportedIndexedMatch outside the reviewed manifest while checking %s\n' \
          "$module"
        printf 'location: %s\n' "$location"
        exit 1
      }
      observed_unsupported["$location"]=1
    fi
    previous_line=$diagnostic_line
  done <<< "$diagnostic"
done

# Fail when an exception becomes stale: removing or moving a warning must also
# update the suppression audit and the corresponding proof-ledger qualification.
for location in "${allowed_unsupported_locations[@]}"; do
  [[ -n ${observed_unsupported["$location"]+present} ]] || {
    printf 'FAIL: documented UnsupportedIndexedMatch was not observed at %s\n' "$location"
    exit 1
  }
done
[[ ${#observed_unsupported[@]} -eq ${#allowed_unsupported_locations[@]} ]] || {
  printf 'FAIL: warning manifest cardinality mismatch (expected %s, observed %s)\n' \
    "${#allowed_unsupported_locations[@]}" "${#observed_unsupported[@]}"
  exit 1
}

printf 'PASS: %s source modules checked; UnsupportedIndexedMatch is confined to %s audited source spans\n' \
  "${#modules[@]}" "${#allowed_unsupported_locations[@]}"
