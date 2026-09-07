#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.."

# Check each source module, including any new module omitted from All.agda.
shopt -s nullglob
modules=(src/EpistemicTypes/*.agda)
[[ ${#modules[@]} -gt 0 ]] || { echo 'FAIL: no proof modules'; exit 1; }
for module in "${modules[@]}"; do
  agda --no-libraries --safe --without-K --double-check --ignore-interfaces \
    -W error -i src "$module"
done
printf 'PASS: %s source modules checked under the required proof discipline\n' "${#modules[@]}"
