#!/usr/bin/env bash
# First-run proof gate for epistemic-types.
#
# Uses a local Agda when one is on PATH; otherwise enters the checked-in Guix
# environment (build/guix.scm). CI (.github/workflows/agda.yml) runs this same
# script inside the pinned Debian 13 container, whose agda-bin version is
# asserted to be 2.6.4.3 before the gates run.
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.."

required_agda=2.6.4.3

run_gates() {
  bash tests/check-proofs.sh
  bash tests/check-rejections.sh
}

# Recursion guard: the Guix environment may resolve a differently named binary;
# if it still lacks agda we fail rather than looping.
if [[ "${EPISTEMIC_TYPES_IN_GUIX:-0}" == 1 ]]; then
  run_gates
  exit 0
fi

if command -v agda >/dev/null 2>&1; then
  version=$(agda --version | sed -n 's/^Agda version //p')
  printf 'INFO: local Agda %s (CI pins %s)\n' "${version:-unknown}" "$required_agda"
  run_gates
elif command -v guix >/dev/null 2>&1; then
  printf 'INFO: no local agda; entering the checked-in Guix environment (build/guix.scm)\n'
  export EPISTEMIC_TYPES_IN_GUIX=1
  exec guix shell -D -f build/guix.scm -- bash scripts/check.sh
else
  cat >&2 <<'EOF'
FAIL: no Agda toolchain found.

Install Agda 2.6.4.3 (the CI-matched version), or run this repository's
dev container (.devcontainer/), or install Guix and re-run:

    guix shell -D -f build/guix.scm -- bash scripts/check.sh
EOF
  exit 1
fi
