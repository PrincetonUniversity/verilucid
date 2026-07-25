# Verifiable Lucid

This repository extends [Dafny](https://dafny.org) with a backend that translates Dafny programs into [Lucid](https://github.com/PrincetonUniversity/lucid) programs.

## Requirements

- Dependencies for Dafny and Lucid, see respective projects for more info

## Quick start

```bash
make setup      # first time only; sets up Dafny and Lucid
make build      # (re)build Dafny with the Lucid backend
make test       # translate and type-check VeriLucid examples
```

## Repository layout

- `src/` -- The Dafny-Lucid backend (`compiler`), libraries (`lib`), and a few lines of glue code for the Dafny repo (`glue`)
- `examples/` — Example Dafny/Lucid programs.
- `scripts/` - setup, build, and test scripts.

*generated directories* 

- `build/` — Generated output from example translations.
- `dafny/` — Local checkout of the pinned Dafny revision. Created by setup; do not edit it directly.
- `lucid/` — Local copy of the Lucid repository and its type checker. Created by setup; do not edit it directly.

