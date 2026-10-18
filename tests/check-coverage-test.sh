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

# check <covered|missing> <name> [missing-module ...]
# Read a Lintel.All fixture from stdin and run the coverage gate with the fake
# prover. For covered fixtures, require exit status 42 and the proof-started
# marker, proving coverage reached the first proof invocation. For missing
# fixtures, require exit status 1, no proof-started marker, and exactly the
# supplied missing-module diagnostics (default: Lintel.Lattice).
# Print PASS with the case name on success; print the captured gate output to
# stderr and exit the test script with status 1 on an assertion failure.
check() {
  local expected="$1" name="$2" status=0 expected_errors actual_errors
  local missing_modules=("${@:3}")
  if [ "${#missing_modules[@]}" -eq 0 ]; then
    missing_modules=(Lintel.Lattice)
  fi
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
  else
    expected_errors="$(printf 'ERROR: %s is not imported by src/Lintel/All.agda\n' "${missing_modules[@]}" | sort)"
    actual_errors="$(grep '^ERROR:' "$fixture/output" | sort || true)"
    if [ "$status" -ne 1 ] || [ -f "$fixture/proof-started" ] ||
      [ "$actual_errors" != "$expected_errors" ]; then
      echo "FAIL: $name did not report exactly the uncovered modules" >&2
      cat "$fixture/output" >&2
      exit 1
    fi
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

# Literal state must survive line boundaries, then end at the closing quote.
check missing 'an import line inside a multiline string is not active' <<'AGDA'
module Lintel.All where
text = "first line
import Lintel.Lattice
last line"
AGDA

check covered 'an active import after a multiline string is detected' <<'AGDA'
module Lintel.All where
text = "first line
{- -- import Lintel.Decoy
last line"
import Lintel.Lattice
AGDA

check missing 'escaped quote keeps a string open across an import line' <<'AGDA'
module Lintel.All where
text = "escaped quote: \"
import Lintel.Lattice
last line"
AGDA

check missing 'closing a multiline string restores block comment handling' <<'AGDA'
module Lintel.All where
text = "first line
last line" {-
import Lintel.Lattice
-}
AGDA

check missing 'closing a multiline string restores line comment handling' <<'AGDA'
module Lintel.All where
text = "first line
last line" -- import Lintel.Lattice
AGDA

check covered 'separate strings do not leak comment state into an import' <<'AGDA'
module Lintel.All where
opening = "{-"
closing = "-}"
line = "--"
import Lintel.Lattice
AGDA

check missing 'removing a string must not join pieces of the import keyword' <<'AGDA'
module Lintel.All where
im"ignored"port Lintel.Lattice
AGDA

check missing 'removing a character must not join pieces of a module name' <<'AGDA'
module Lintel.All where
import Lintel.Lat'x'tice
AGDA

check missing 'a second block comment still hides an import after the first closes' <<'AGDA'
module Lintel.All where
{- first -} {- second
import Lintel.Lattice
-}
AGDA

check covered 'a trailing multiline nested comment preserves an active import' <<'AGDA'
module Lintel.All where
import Lintel.Lattice {- outer
{- inner -}
import Lintel.Decoy
-}
AGDA

check missing 'an unclosed block comment cannot supply coverage' <<'AGDA'
module Lintel.All where
{- unclosed
import Lintel.Lattice
AGDA

check missing 'an unclosed string cannot supply coverage' <<'AGDA'
module Lintel.All where
text = "unclosed
import Lintel.Lattice
AGDA

check missing 'the import keyword is case sensitive' <<'AGDA'
module Lintel.All where
Import Lintel.Lattice
AGDA

check missing 'the imported module name is case sensitive' <<'AGDA'
module Lintel.All where
import Lintel.lattice
AGDA

# Exercise delimiter boundaries where comment and literal states interact.
check covered 'an empty block comment separates import tokens' <<'AGDA'
module Lintel.All where
import{--}Lintel.Lattice
AGDA

check missing 'a block comment opener cannot overlap its closing delimiter' <<'AGDA'
module Lintel.All where
{-}
import Lintel.Lattice
AGDA

check covered 'backslashes inside a block comment do not escape its closer' <<'AGDA'
module Lintel.All where
{- explanation \-} import Lintel.Lattice
AGDA

check covered 'line-comment text inside a block comment still allows nesting' <<'AGDA'
module Lintel.All where
{- outer
-- {- inner
-}
-} import Lintel.Lattice
AGDA

check covered 'a trailing backslash does not continue a line comment' <<'AGDA'
module Lintel.All where
-- explanation \
import Lintel.Lattice
AGDA

check covered 'an escaped double quote character does not open a string' <<'AGDA'
module Lintel.All where
quote = '\"'
import Lintel.Lattice
AGDA

check missing 'a comment after an escaped double quote character still hides imports' <<'AGDA'
module Lintel.All where
quote = '\"' {-
import Lintel.Lattice
-}
AGDA

check missing 'an escaped backslash before an escaped quote keeps a string open' <<'AGDA'
module Lintel.All where
text = "backslash and quote: \\\"
import Lintel.Lattice
last line"
AGDA

check missing 'code after a closed trailing comment is not discarded' <<'AGDA'
module Lintel.All where
import Lintel.Lattice {- explanation -}Extra
AGDA

# Keep CRLFs and the missing final newline visible in the test definition.
printf 'module Lintel.All where\r\n{- outer\r\n{- inner -}\r\n-}\timport\tLintel.Lattice-- trailing' |
  check covered 'nested comments and a trailing line comment with CRLF at EOF'

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

check missing 'duplicate imports cannot cover a different missing module' Lintel.Nested.Extra <<'AGDA'
module Lintel.All where
import Lintel.Lattice
import Lintel.Lattice
{- import Lintel.Nested.Extra -}
AGDA

check missing 'imports in a multiline string cannot cover either module' \
  Lintel.Lattice Lintel.Nested.Extra <<'AGDA'
module Lintel.All where
text = "imports in a string
import Lintel.Lattice
import Lintel.Nested.Extra
end of string"
AGDA

check missing 'every missing module is reported when all imports are commented' \
  Lintel.Lattice Lintel.Nested.Extra <<'AGDA'
module Lintel.All where
{-
import Lintel.Lattice
{- import Lintel.Nested.Extra -}
-}
AGDA

check covered 'one comment can close before an import and reopen around another' <<'AGDA'
module Lintel.All where
{- before
-} import Lintel.Lattice {- after
import Lintel.Nested.Extra
-}
import Lintel.Nested.Extra
AGDA

# Agda names may contain apostrophes (a name part is letters, digits and '-_),
# so a quoted run inside a module name is part of the name, not a character
# literal. Recognising literals only at a token boundary is what keeps an
# active `import Lintel.Foo'X'` intact; recognising them anywhere rewrites it
# to `import Lintel.Foo` and reports the module uncovered.
check covered 'a character literal after an apostrophe-suffixed name is still a literal' <<'AGDA'
module Lintel.All where
label' = 'x'
import Lintel.Lattice
import Lintel.Nested.Extra
AGDA

touch "$fixture/src/Lintel/Foo'X'.agda"

check covered 'an active import whose module name contains apostrophes' <<'AGDA'
module Lintel.All where
import Lintel.Lattice
import Lintel.Nested.Extra
import Lintel.Foo'X'
AGDA

check missing 'an apostrophe-named module is not covered when its import is commented' \
  "Lintel.Foo'X'" <<'AGDA'
module Lintel.All where
import Lintel.Lattice
import Lintel.Nested.Extra
{- import Lintel.Foo'X' -}
AGDA

check missing 'a lookalike name without the apostrophes does not cover the module' \
  "Lintel.Foo'X'" <<'AGDA'
module Lintel.All where
import Lintel.Lattice
import Lintel.Nested.Extra
import Lintel.FooX
AGDA
