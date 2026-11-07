#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
# Cross-repository checks stay separate from the builtins-only core gate.
set -euo pipefail
if [[ $# -ne 2 ]]; then
  printf 'Usage: bash scripts/check-canonical.sh ECHO_ROOT STDLIB_SRC\n' >&2
  exit 64
fi
echo_root=$(cd -- "$1" && pwd)
stdlib_src=$(cd -- "$2" && pwd)
cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.."
prover=${AGDA:-agda}
for dependency in "$echo_root/proofs/agda/Echo.agda" \
                  "$echo_root/proofs/agda/EchoResidue.agda" \
                  "$echo_root/proofs/agda/EchoFiniteResidue.agda" \
                  "$stdlib_src/Data/Fin/Properties.agda"; do
  [[ -r $dependency ]] || { printf 'FAIL: missing dependency: %s\n' "$dependency" >&2; exit 1; }
done
"$prover" --version
# Retain the integration job's existing UnsupportedIndexedMatch policy.
# Success does not assert Cubical transport computation for indexed matches.
# Each first-party module also declares exact-split/no-sized-types/no-guardedness.
# Do not impose those local options on the independently maintained stdlib.
# RecoveryExamples imports CanonicalEcho, CanonicalRecovery and
# CanonicalPartialRecovery: one cold closure checks all four policy-manifest
# modules without rechecking the same standard library four times.
"$prover" --no-libraries --safe --without-K --cubical-compatible \
  --double-check --ignore-interfaces \
  -W error -W noUnsupportedIndexedMatch -i src -i tests/integration \
  -i "$echo_root/proofs/agda" -i "$stdlib_src" tests/integration/RecoveryExamples.agda
