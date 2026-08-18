### NOTE (8/17/2026) we are in the middle of cleaning up / documenting / syncing this repository with the paper. Proceed with caution!

# VeriLucid

This is the repository for VeriLucid, a dialect of [Dafny](https://dafny.org) for data-plane programming that compiles to [Lucid](https://github.com/PrincetonUniversity/lucid). See the [VeriLucid paper](https://dl.acm.org/doi/10.1145/3789240.3829171) for more details.

This repo contains: 1) libraries that represent Lucid's data-plane primitives in Dafny; 2) a Dafny backend that translates Dafny programs into Lucid; and 3) examples.

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

*generated directories (from make setup and build)* 

- `build/` — Generated output from example translations.
- `dafny/` — Local checkout of the pinned Dafny revision. Created by setup; do not edit it directly.
- `lucid/` — Local copy of the Lucid repository and its type checker. Created by setup; do not edit it directly.

