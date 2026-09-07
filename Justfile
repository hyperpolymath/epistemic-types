check: check-proofs check-rejections

check-proofs:
	bash tests/check-proofs.sh

check-rejections:
	bash tests/check-rejections.sh

# Optional integration gate: actual echo-types checkout and stdlib source.
check-canonical echo_root stdlib_src:
	agda --no-libraries --safe --without-K --double-check --ignore-interfaces -W error -W noUnsupportedIndexedMatch -i src -i tests/integration -i '{{echo_root}}/proofs/agda' -i '{{stdlib_src}}' tests/integration/CanonicalEcho.agda

# Build/test/validate include positive proofs and semantic rejection controls.
build: check
test: check
validate: check

default: check
