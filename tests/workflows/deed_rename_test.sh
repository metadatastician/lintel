#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# scripts/repo-deed.sh is the one place that finds and renames the repo deed at
# mint. repo-init is carried into children unchanged, so the name it renames
# FROM is the parent's slug, never a fixed template's: the hardcoded
# rsr-template-repo_chora.deed made every second-generation mint rename nothing
# and then abort at the identity step (measured on lintel, 2026-10-19).
set -euo pipefail
repo=$(git rev-parse --show-toplevel)
script="$repo/scripts/repo-deed.sh"
fixture=$(mktemp -d)
trap 'rm -rf "$fixture"' EXIT

fail() { echo "FAIL: $*" >&2; exit 1; }

# find: the current deed's name is reported, whatever the parent was called.
mkdir -p "$fixture/find"
printf '(repo-deed)\n' > "$fixture/find/lintel_chora.deed"
[ "$(bash "$script" find "$fixture/find")" = "$fixture/find/lintel_chora.deed" ] \
  || fail 'find did not report the deed that is present'
echo 'PASS: find reports the deed whatever the parent slug was'

# rename: a minted repo's deed is renamed to the child's slug.
mkdir -p "$fixture/rename"
printf '(repo-deed :canonical-name "lintel")\n' > "$fixture/rename/lintel_chora.deed"
out="$(bash "$script" rename "$fixture/rename" mint-check)"
[ "$out" = "$fixture/rename/mint-check_chora.deed" ] || fail "rename printed '$out'"
[ -f "$fixture/rename/mint-check_chora.deed" ] || fail 'renamed deed does not exist'
[ ! -e "$fixture/rename/lintel_chora.deed" ] || fail 'the old deed filename survived'
grep -q '"lintel"' "$fixture/rename/mint-check_chora.deed" \
  || fail 'rename changed file content; it must only move the file'
echo 'PASS: a parent-named deed is renamed to the child slug, content untouched'

# Idempotence: a second mint step (or a resumed mint) must not fail.
before="$(ls "$fixture/rename")"
[ "$(bash "$script" rename "$fixture/rename" mint-check)" = "$fixture/rename/mint-check_chora.deed" ] \
  || fail 'rename is not idempotent'
[ "$(ls "$fixture/rename")" = "$before" ] || fail 'idempotent rename changed the directory'
echo 'PASS: rename is idempotent'

# A deed already named for the child is found and left alone.
[ "$(bash "$script" find "$fixture/rename")" = "$fixture/rename/mint-check_chora.deed" ] \
  || fail 'find missed an already-correct deed'
echo 'PASS: an already-correct deed is found'

# No deed is a loud failure, not an empty string the mint silently carries.
mkdir -p "$fixture/none"
if bash "$script" find "$fixture/none" 2>/dev/null; then fail 'find accepted a tree with no deed'; fi
if bash "$script" rename "$fixture/none" mint-check 2>/dev/null; then fail 'rename accepted a tree with no deed'; fi
echo 'PASS: a missing deed fails loudly'

# Two deeds are ambiguous: the deed manifests ONE repository.
mkdir -p "$fixture/two"
printf '(repo-deed)\n' > "$fixture/two/a_chora.deed"
printf '(repo-deed)\n' > "$fixture/two/b_chora.deed"
if bash "$script" find "$fixture/two" 2>/dev/null; then fail 'find accepted two deeds'; fi
if bash "$script" rename "$fixture/two" mint-check 2>/dev/null; then fail 'rename accepted two deeds'; fi
[ -f "$fixture/two/a_chora.deed" ] && [ -f "$fixture/two/b_chora.deed" ] \
  || fail 'ambiguous rename moved a file anyway'
echo 'PASS: two deeds are refused and nothing is moved'

# A slug that cannot be a filename (or a deed stem) is refused.
if bash "$script" rename "$fixture/rename" '../escape' 2>/dev/null; then fail 'rename accepted a path traversal slug'; fi
if bash "$script" rename "$fixture/rename" '' 2>/dev/null; then fail 'rename accepted an empty slug'; fi
[ -f "$fixture/rename/mint-check_chora.deed" ] || fail 'a refused rename still moved the deed'
echo 'PASS: an invalid slug is refused before anything moves'

# Usage errors are distinguishable from "no deed".
rc=0; bash "$script" 2>/dev/null || rc=$?
[ "$rc" -eq 2 ] || fail "no subcommand exited $rc, want 2"
rc=0; bash "$script" rename "$fixture/rename" 2>/dev/null || rc=$?
[ "$rc" -eq 2 ] || fail "incomplete rename exited $rc, want 2"
echo 'PASS: usage errors exit 2'

# repo-init must call this script for both operations rather than name a deed
# itself; a regression to a hardcoded filename would pass every case above.
grep -q 'scripts/repo-deed.sh rename' "$repo/build/just/repo-init.just" \
  || fail 'repo-init no longer renames the deed through scripts/repo-deed.sh'
grep -q 'scripts/repo-deed.sh find' "$repo/build/just/repo-init.just" \
  || fail 'repo-init no longer finds the deed through scripts/repo-deed.sh'
if grep -nE '[A-Za-z0-9_-]+_chora\.deed' "$repo/build/just/repo-init.just" | grep -v '^[0-9]*: *#'; then
  fail 'repo-init names a deed filename directly again'
fi
echo 'PASS: repo-init delegates deed discovery to the tested script'

echo 'PASS: repo deed lookup and rename'
