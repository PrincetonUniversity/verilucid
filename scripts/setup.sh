#!/usr/bin/env bash
# filepath: /Users/johnsonchack/Desktop/gits/verifiable-lucid/compiler/compiler-new/scripts/setup.sh
set -euo pipefail

DAFNY_REPO="https://github.com/dafny-lang/dafny"
PIN=fcb2042d6d043a2634f0854338c08feeaaaf4ae2

cd "$(dirname "$0")/.."

if [ -d dafny/.git ] &&
   [ "$(git -C dafny rev-parse HEAD)" = "$PIN" ] &&   
   git -C dafny apply --reverse --check ../src/glue/register-lucid-backend.patch 2>/dev/null; then
  echo "Setup is already complete. Run 'make build'."
  exit 0
fi

git clone "$DAFNY_REPO" dafny
git -C dafny checkout --quiet "$PIN"
git -C dafny submodule update --init --recursive --quiet

JAR_REL="$(grep -oE 'DafnyRuntimeJava/build/libs/DafnyRuntime-[0-9.]+\.jar' \
  dafny/Source/DafnyRuntime/DafnyRuntime.csproj | head -1)"
JAR="dafny/Source/DafnyRuntime/$JAR_REL"
mkdir -p "$(dirname "$JAR")"
: > "$JAR"

( cd dafny && make exe )

git -C dafny apply ../src/glue/register-lucid-backend.patch
echo "Setup complete. make with 'make build'"