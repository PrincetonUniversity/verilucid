#!/usr/bin/env bash
# filepath: /Users/johnsonchack/Desktop/gits/verifiable-lucid/compiler/compiler-new/scripts/updatebackend.sh
# Copy VeriLucid sources into the local Dafny directory.
# Called by `make build`.
set -euo pipefail

cd "$(dirname "$0")/.."

dst_dir=./dafny/Source/DafnyCore/Backends/Lucid
ast_copy="$dst_dir/AST.dfy"

mkdir -p "$dst_dir"

# Backend sources
cp ./src/compiler/*.dfy "$dst_dir"/

# Dafny's DAST is already in scope in this directory.
for file in "$dst_dir"/*.dfy; do
  sed -i '' '1{/^include "AST\.dfy"$/d;}' "$file"
done
rm -f "$ast_copy"

# C# glue
cp ./src/glue/*.cs "$dst_dir"/
