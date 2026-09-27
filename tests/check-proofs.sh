#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.."

# Check each source module, including any new module omitted from All.agda.
# The search is recursive so that modules in subdirectories (for example the
# Applications/ tree) are gated even when they are not re-exported by All.agda.
mapfile -t modules < <(find src/EpistemicTypes -name '*.agda' | sort)
[[ ${#modules[@]} -gt 0 ]] || { echo 'FAIL: no proof modules'; exit 1; }
for module in "${modules[@]}"; do
  agda --no-libraries --safe --without-K --double-check --ignore-interfaces \
    -W error -i src "$module"
done
printf 'PASS: %s source modules checked under the required proof discipline\n' "${#modules[@]}"
