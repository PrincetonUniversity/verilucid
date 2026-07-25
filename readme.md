# Verifiable Lucid Compiler

This repository extends [Dafny](https://dafny.org) with a backend that translates Dafny programs into Lucid (`.dpt`) programs.

## Repository layout

- `src/compiler/` — Dafny source files for the Lucid backend.
- `src/glue/` — C# glue code and the patch that registers the backend with Dafny.
- `src/lib/` — Dafny library definitions used by Lucid programs.
- `examples/` — Example Dafny/Lucid programs.
- `scripts/setup.sh` — One-time bootstrap script for the pinned Dafny checkout.
- `scripts/setup_lucid.sh` — One-time bootstrap script for the Lucid type checker.
- `scripts/updatebackend.sh` — Copies backend and glue sources into the local Dafny checkout.
- `scripts/test.sh` — Translates and type-checks the example programs.
- `dafny/` — Local checkout of the pinned Dafny revision. Created by setup; do not edit it directly.
- `lucid/` — Local copy of the Lucid repository and its type checker. Created by setup; do not edit it directly.
- `build/` — Generated output from example translations.

## Requirements

- Git
- Dependencies required to build Dafny, including the .NET SDK
- Dependencies required to build Lucid

## Setup

From the repository root:

```bash
make setup
```

This:

1. Clones Dafny into `dafny/`.
2. Checks out the pinned Dafny revision.
3. Builds stock Dafny.
4. Applies the patch that registers the Lucid backend.
5. Clones Lucid into `lucid/`.
6. Removes Lucid's `.git` directory, making it a local source copy rather than a nested Git repository.
7. Builds the Lucid `dpt` type checker.

Setup is intended to run once. The scripts detect an already-completed Dafny or Lucid setup and exit successfully.

## Build

Build the Lucid-enabled Dafny compiler:

```bash
make build
```

This copies the sources from `src/compiler/` and `src/glue/` into the local Dafny checkout, regenerates Dafny's generated C# code, and rebuilds Dafny.

Run `make build` after changing files in `src/compiler/` or `src/glue/`.

## Test

Run the example regression tests:

```bash
make test
```

Tests translate each selected program in `examples/` to Lucid and run the Lucid type checker on the generated `.dpt` output.

Tests require a completed build. If the Lucid-enabled Dafny compiler is unavailable, run:

```bash
make build
```

## Development workflow

```bash
make setup      # first time only; sets up Dafny and Lucid
make build      # after backend or glue changes
make test       # translate and type-check examples
```

Dafny examples can include the Lucid builtin library with:

```dafny
include "../src/lib/lucidLibrary.dfy"
```

Do not make persistent changes directly under `dafny/` or `lucid/`. Make backend changes in `src/compiler/`, C# integration changes in `src/glue/`, then run `make build`.