check:
	agda --no-libraries -i src src/EpistemicTypes/All.agda

# build / test / validate all reduce to the single proof check: the library's
# correctness IS that All.agda type-checks under --safe --without-K.
build: check
test: check
validate: check

default: check
