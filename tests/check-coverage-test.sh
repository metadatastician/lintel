#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0

set -euo pipefail

root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
fixture="$(mktemp -d)"
trap 'rm -rf "$fixture"' EXIT
mkdir -p "$fixture/scripts" "$fixture/src/Lintel" "$fixture/sibling"
cp "$root/scripts/check.sh" "$fixture/scripts/check.sh"
touch "$fixture/src/Lintel/Lattice.agda"

# Stop at the first proof invocation: these fixtures test coverage only.
cat > "$fixture/agda" <<'AGDA'
#!/usr/bin/env bash
if [ "${1:-}" = --version ]; then
  echo 'Agda version 2.6.4.3'
  exit 0
fi
touch "${0%/*}/proof-started"
exit 42
AGDA
chmod +x "$fixture/agda"

check() {
  local expected="$1" name="$2" status=0
  cat > "$fixture/src/Lintel/All.agda"
  rm -f "$fixture/proof-started"
  AGDA="$fixture/agda" AGDA_VERSION=2.6.4.3 SECRET_TYPES_SRC="$fixture/sibling" \
    bash "$fixture/scripts/check.sh" > "$fixture/output" 2>&1 || status=$?
  if [ "$expected" = covered ]; then
    if [ "$status" -ne 42 ] || [ ! -f "$fixture/proof-started" ]; then
      echo "FAIL: $name did not reach the proof check" >&2
      cat "$fixture/output" >&2
      exit 1
    fi
  elif [ "$status" -ne 1 ] || [ -f "$fixture/proof-started" ] ||
    ! grep -q '^ERROR: Lintel.Lattice is not imported' "$fixture/output"; then
    echo "FAIL: $name did not reject the uncovered module" >&2
    cat "$fixture/output" >&2
    exit 1
  fi
  echo "PASS: $name"
}

check covered 'active import' <<'AGDA'
{-# OPTIONS --safe --without-K #-}
module Lintel.All where
import Lintel.Lattice
AGDA

check missing 'block-commented import' <<'AGDA'
module Lintel.All where
{-
import Lintel.Lattice
-}
AGDA

check missing 'nested block-commented import' <<'AGDA'
module Lintel.All where
{- outer {- inner -}
import Lintel.Lattice
-}
AGDA

check missing 'line-commented import' <<'AGDA'
module Lintel.All where
-- import Lintel.Lattice
AGDA

check missing 'absent import' <<'AGDA'
module Lintel.All where
AGDA

check missing 'different module' <<'AGDA'
module Lintel.All where
import Lintel.LatticeExtra
AGDA

check covered 'active import after line comment with a block opener' <<'AGDA'
module Lintel.All where
-- {- is not a block comment here
import Lintel.Lattice
AGDA

check covered 'active import after a block comment with line-comment text' <<'AGDA'
module Lintel.All where
{- outer
-- -} import Lintel.Lattice
AGDA

check covered 'active import with inline comments' <<'AGDA'
module Lintel.All where
{- before -} import {- between -} Lintel.Lattice {- after -} -- trailing
AGDA

check covered 'comment delimiters in literals' <<'AGDA'
module Lintel.All where
text = "\" {- --"
quote = '"'
import Lintel.Lattice
AGDA

check missing 'block opener in a string before a commented import' <<'AGDA'
module Lintel.All where
text = "{-"
{-
import Lintel.Lattice
-}
AGDA

check missing 'comment must not join tokens into an import' <<'AGDA'
module Lintel.All where
im{- comment -}port Lintel.Lattice
AGDA
