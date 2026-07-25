# One-time: create the pinned Dafny sandbox, apply patches, sync backend + glue.
setup:
	./scripts/setup.sh
	./scripts/setup_lucid.sh

# Rebuild the dafny+Lucid compiler: sync backend sources, regenerate C# from
# the Dafny backend, then rebuild the dafny exe.
build: setup
	./scripts/updatebackend.sh
	echo "rebuilding dafny extensions to dafny compiler"
	cd dafny/Source/DafnyCore && ./DafnyGeneratedFromDafny.sh --no-verify
	echo "rebuilding dafny compiler"
	cd dafny && make exe

test:
	./scripts/test.sh


.PHONY: test