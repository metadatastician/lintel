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
  local expected="$1" name="$2" missing_module="${3:-Lintel.Lattice}" status=0
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
    ! grep -Fxq "ERROR: $missing_module is not imported by src/Lintel/All.agda" "$fixture/output"; then
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

# Generate significant whitespace explicitly so formatting cannot erase it.
printf 'module Lintel.All where\n  import   Lintel.Lattice  \n' |
  check covered 'leading, separating and trailing spaces'

printf 'module Lintel.All where\n\timport\tLintel.Lattice\t\n' |
  check covered 'leading, separating and trailing tabs'

printf 'module Lintel.All where\r\nimport Lintel.Lattice\r\n' |
  check covered 'CRLF line endings'

printf 'module Lintel.All where\nimport Lintel.Lattice' |
  check covered 'import at EOF without a final newline'

check missing 'empty aggregator' < /dev/null

check missing 'import keyword requires a separator' <<'AGDA'
module Lintel.All where
importLintel.Lattice
AGDA

check missing 'module dots are literal rather than regex wildcards' <<'AGDA'
module Lintel.All where
import LintelXLattice
AGDA

check missing 'a child module does not cover its parent' <<'AGDA'
module Lintel.All where
import Lintel.Lattice.Extra
AGDA

check missing 'import-like text after other code' <<'AGDA'
module Lintel.All where
text = "prefix"; import Lintel.Lattice
AGDA

check missing 'comment must not join pieces of a module name' <<'AGDA'
module Lintel.All where
import Lintel.Lat{- comment -}tice
AGDA

check covered 'active import following a commented duplicate' <<'AGDA'
module Lintel.All where
{- import Lintel.Lattice -}
import Lintel.Lattice
AGDA

check covered 'trailing line comment needs no preceding space' <<'AGDA'
module Lintel.All where
import Lintel.Lattice-- explanation
AGDA

check covered 'adjacent inline comments separate import tokens' <<'AGDA'
module Lintel.All where
{- one -}{- two -}import{- three -}{- four -}Lintel.Lattice{- five -}
AGDA

check covered 'all nested comment levels close before the active import' <<'AGDA'
module Lintel.All where
{- outer
{- middle {- inner -}
import Lintel.Decoy
-}
-} import Lintel.Lattice
AGDA

check missing 'closing an inner comment does not end the outer comment' <<'AGDA'
module Lintel.All where
{- outer
{- inner -}
import Lintel.Lattice
-}
AGDA

check covered 'quotes inside block comments do not enter literal state' <<'AGDA'
module Lintel.All where
{- " '\"' -}
import Lintel.Lattice
AGDA

check covered 'quotes inside line comments do not affect the next line' <<'AGDA'
module Lintel.All where
-- " '\"' {-
import Lintel.Lattice
AGDA

check covered 'closing comment delimiters in a string stay literal' <<'AGDA'
module Lintel.All where
text = "-} {- --"
import Lintel.Lattice
AGDA

check covered 'escaped backslash does not escape the closing string quote' <<'AGDA'
module Lintel.All where
text = "\\"
import Lintel.Lattice
AGDA

check missing 'comment after an escaped-backslash string still hides imports' <<'AGDA'
module Lintel.All where
text = "\\"
{-
import Lintel.Lattice
-}
AGDA

check covered 'escaped character literals do not affect the next import' <<'AGDA'
module Lintel.All where
apostrophe = '\''
backslash = '\\'
newline = '\n'
import Lintel.Lattice
AGDA

check missing 'character quote does not hide the following block comment' <<'AGDA'
module Lintel.All where
quote = '"'
{-
import Lintel.Lattice
-}
AGDA

check missing 'apostrophes in identifiers do not hide block comments' <<'AGDA'
module Lintel.All where
label' = "text"
{-
import Lintel.Lattice
-}
AGDA

# The same stripped imports must cover every discovered module independently.
mkdir -p "$fixture/src/Lintel/Nested"
touch "$fixture/src/Lintel/Nested/Extra.agda"

check covered 'multiple modules including a nested namespace' <<'AGDA'
module Lintel.All where
  import Lintel.Lattice
  import {- explanation -} Lintel.Nested.Extra
AGDA

check missing 'covered parent does not mask a commented nested module' Lintel.Nested.Extra <<'AGDA'
module Lintel.All where
import Lintel.Lattice
{- import Lintel.Nested.Extra -}
AGDA

check missing 'covered nested module does not mask an uncovered parent' <<'AGDA'
module Lintel.All where
-- import Lintel.Lattice
import Lintel.Nested.Extra
AGDA
