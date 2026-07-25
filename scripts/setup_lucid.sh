#!/usr/bin/env bash
# filepath: /Users/johnsonchack/Desktop/gits/verifiable-lucid/compiler/compiler-new/scripts/setup_lucid.sh
set -euo pipefail

cd "$(dirname "$0")/.."

if [ -f lucid/dpt ]; then
  echo "Lucid is already built."
  exit 0
fi

git clone https://github.com/princetonuniversity/lucid lucid
rm -rf lucid/.git

make -C lucid