#!/usr/bin/env bash
#
# Regression test: run each example through the Dafny->Lucid compiler and then
# the Lucid type checker. An example PASSES only if it translates with no error
# markers and the resulting .dpt type checks.
#
# Add examples to the EXAMPLES list below.

set -u
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
DAFNY="$ROOT/dafny/Scripts/dafny"
DPT="$ROOT/lucid/dpt"
EXAMPLE_DIR="$ROOT/examples"
BUILD_DIR="$ROOT/build"

if ! "$DAFNY" translate dpt --help; then
  echo "Please run make build first to build the Dafny+Lucid compiler."
  exit 1
fi


EXAMPLES=(  
  # sigcomm paper eval programs
  $EXAMPLE_DIR/bf.dfy
  $EXAMPLE_DIR/sbf.dfy
  $EXAMPLE_DIR/countMin.dfy
  $EXAMPLE_DIR/macLearner.dfy
  $EXAMPLE_DIR/ontas.dfy
  $EXAMPLE_DIR/turboflow.dfy
  $EXAMPLE_DIR/simpleSwitchML.dfy
  # other test programs
  $EXAMPLE_DIR/maclearner-with-records.dfy
  $EXAMPLE_DIR/bfMinimal.dfy
  $EXAMPLE_DIR/seqTest.dfy
)

pass=0
fail=0
failed=()

for ex in "${EXAMPLES[@]}"; do
  name="$(basename "$ex" .dfy)" # name of the input file
  ex_dir="$(dirname "$ex")"     # directory of the input file
  local_build_dir="${name}-Lucid" # local build dir for the example

  dst_build_dir="$BUILD_DIR/$local_build_dir" # destination build dir for the example
  out="$dst_build_dir/src/${name}.dpt" # destination output file for the example

  # 0. Clean up any previous build artifacts.
  rm -rf "$dst_build_dir"
  mkdir -p "$dst_build_dir"

  # 1. Translate. Run from the example's directory so relative `include`s
  #    (e.g. lucidLibrary.dfy) resolve.
  ( cd "$ex_dir" \
    && "$DAFNY" translate dpt --no-verify:true --allow-warnings "${name}.dfy"  >/dev/null 2>&1 \
    && mv "$local_build_dir" $BUILD_DIR )

  # 2. check if the local build dir has the expected output file.
  if [[ ! -f "$out" ]]; then
    echo "FAIL  $ex  (no .dpt produced)"
    fail=$((fail + 1)); failed+=("$ex"); continue
  fi

  # 3. Translation errors and unimplemented features are left as marker
  #    comments in the output rather than a non-zero exit.
  if grep -qE "error translating|unsupported|TODO: emit" "$out"; then
    echo "FAIL  $ex  (translation left error/stub markers; see $out)"
    fail=$((fail + 1)); failed+=("$ex"); continue
  fi

  # 4. Lucid type check.
  if "$DPT" "$out" >/dev/null 2>&1; then
    echo "PASS  $ex"
    pass=$((pass + 1))
  else
    echo "FAIL  $ex  (lucid type check failed; run: $DPT $out)"
    fail=$((fail + 1)); failed+=("$ex")
  fi
done

echo "-----"
echo "$pass passed, $fail failed"
[[ $fail -eq 0 ]]