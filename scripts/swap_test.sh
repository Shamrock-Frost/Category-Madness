#!/usr/bin/env bash
# The swap test (D-TL-06 (4), D-CH-12, D-RT-13 (4)).
#
# Build Theory/ against Interface-Stub/, a copy of Interface/ in which every constant is
# a bodiless `axiom` with the same statement. Green means Theory/ depends on nothing but
# the statements: no leak of definitional equalities from Kernel/ or Root/.
#
# Mechanism: Interface-Stub/ is not a lake target (two libraries cannot both own the
# module namespace `Interface.*`). The test swaps the directories, rebuilds, and swaps
# back — it must run on a clean checkout, never on a working tree with local edits.
set -euo pipefail
cd "$(dirname "$0")/.."

if ! ls Theory/**/*.lean Theory/*.lean >/dev/null 2>&1; then
  echo "swap_test: Theory/ has no Lean sources yet; nothing to test (M0 scaffolding)."
  exit 0
fi
if [ ! -f Interface-Stub/Interface.lean ]; then
  echo "swap_test: Interface-Stub/ is missing or not generated (scripts/gen_stub, M3)." >&2
  exit 1
fi

cleanup() {
  if [ -d Interface.real ]; then
    rm -rf Interface && mv Interface.real Interface
  fi
}
trap cleanup EXIT

mv Interface Interface.real
cp -r Interface-Stub Interface
lake build Theory
echo "swap_test: Theory/ builds against the stub interface — no leak."
