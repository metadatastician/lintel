#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
#
# The Agda proof gate.  Pattern: choreographic-types / residual-evidence-types
# scripts/check.sh.  Run scripts/fetch-siblings.sh first.
#
# Every check runs with --safe --without-K --no-libraries --ignore-interfaces
# --double-check -W error: no library resolution (siblings come in as explicit
# -i paths at their pins), no stale .agdai standing in for a proof, the kernel
# re-verifies every term, and a warning is a failure.
#
#   1. coverage: every module under src/Lintel is imported by Lintel.All
#   2. the pinned sibling's development (SecretTypes.All, TINI included)
#   3. Lintel's proofs (Lintel.All)
#   4. positive controls: every tests/accept module typechecks
#   5. expected rejections: every tests/reject module fails AT its `invalid`
#      declaration with a type mismatch, never for a missing import or a
#      parse error
#   6. negative control: the rejection check, pointed at each positive
#      control, reports it accepted, so step 5 cannot pass vacuously
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.."
export LC_ALL="${LC_ALL:-C.UTF-8}"

prover="${AGDA:-agda}"
expected_version="${AGDA_VERSION:-2.6.4.3}"
deps="${DEPENDENCIES_DIR:-_build/dependencies}"
st="${SECRET_TYPES_SRC:-$deps/secret-types/src}"

if [ ! -d "$st" ]; then
  echo "ERROR: secret-types sources not found at $st (run scripts/fetch-siblings.sh or set SECRET_TYPES_SRC)" >&2
  exit 1
fi

version="$("$prover" --version)"
echo "$version"
if [ "$version" != "Agda version $expected_version" ]; then
  echo "ERROR: expected 'Agda version $expected_version' (the Debian pin); set AGDA_VERSION to check with another" >&2
  exit 1
fi

flags=(--safe --without-K --no-libraries --ignore-interfaces --double-check -W error -i src -i "$st")

# 1. Coverage: a module that Lintel.All does not import is never checked.
# Strip nested Agda comments once, before looking for active imports.
#
# A character literal is recognised only at a token boundary: Agda names may
# contain apostrophes and most non-whitespace Unicode characters
# (agda.readthedocs.io, Lexical structure), so in `import Lintel.FooΔ'X'` the
# quoted run is part of the module name, not a literal. Stripping it would
# rewrite a real import into `import Lintel.FooΔ` and report the module
# uncovered. `prev` is the last character emitted as code; an empty `prev`
# is the start of the line, and a space is what a stripped comment, string or
# literal leaves behind, so both count as boundaries, as do Agda special
# symbols: .;{}()@".
imports="$(awk '
  {
    code = ""
    prev = ""
    for (i = 1; i <= length($0); i++) {
      c = substr($0, i, 1); pair = substr($0, i, 2)
      if (depth) {
        if (pair == "{-") { depth++; i++ }
        else if (pair == "-}") { depth--; i++ }
      } else if (quoted) {
        if (c == "\\") i++
        else if (c == "\"") quoted = 0
      } else if (pair == "--") {
        break
      } else if (pair == "{-") {
        depth++; i++; code = code " "; prev = " "
      } else if (c == "\"") {
        quoted = 1; code = code " "; prev = " "
      } else if (c == "\047" && (prev == "" || prev ~ /[[:space:].;{}()@"]/) &&
                 match(substr($0, i), /^\047([^\047\\]|\\.)\047/)) {
        i += RLENGTH - 1; code = code " "; prev = " "
      } else {
        code = code c; prev = c
      }
    }
    print code
  }
' src/Lintel/All.agda)"
missing=0
while IFS= read -r file; do
  module="${file#src/}"; module="${module%.agda}"; module="${module//\//.}"
  [ "$module" = Lintel.All ] && continue
  # The module name is literal text, not a regular expression.  Agda names may
  # carry `.`, `+`, `*`, `(`, `|` and friends, and only `.` was escaped, so
  # `Lintel.Operator+'X'` never matched itself: `Operator+` reads as "Operato,
  # then one or more r".  Compare literally instead of building a pattern — the
  # only regular expression left is the `import` keyword and its separator.
  if ! awk -v mod="$module" '
        {
          line = $0
          sub(/^[[:space:]]+/, "", line)
          if (line !~ /^import[[:space:]]+/) next
          sub(/^import[[:space:]]+/, "", line)
          sub(/[[:space:]]+$/, "", line)
          if (line == mod) found = 1
        }
        END { exit found ? 0 : 1 }' <<< "$imports"; then
    echo "ERROR: $module is not imported by src/Lintel/All.agda" >&2
    missing=1
  fi
done < <(find src/Lintel -name '*.agda' | sort)
(( missing == 0 )) || exit 1
echo 'PASS: every module under src/Lintel is imported by Lintel.All'

# 2. The sibling at its pin, under this gate's flags.
"$prover" "${flags[@]}" "$st/SecretTypes/All.agda"
echo 'PASS: secret-types at its pin (SecretTypes.All, TINI included)'

# 3. Lintel's proofs.
"$prover" "${flags[@]}" src/Lintel/All.agda
echo 'PASS: Lintel proofs (Lintel.All)'

mkdir -p _build/check-logs

# expect_rejected <file>
# Succeeds iff <file> fails to typecheck AT its `invalid` declaration with a
# type mismatch.  Otherwise prints the reason (and the log for an unexpected
# failure) and returns 1.
expect_rejected() {
  local file="$1" name log invalid_line diag_line
  name="$(basename -- "$file" .agda)"
  log="_build/check-logs/$name.log"
  if "$prover" "${flags[@]}" -i "$(dirname -- "$file")" "$file" >"$log" 2>&1; then
    echo "invalid proof accepted: $name"
    return 1
  fi
  invalid_line="$(grep -nE '^invalid ' "$file" | head -1 | cut -d: -f1)"
  diag_line="$(grep -oE "/$name\.agda:[0-9]+,[0-9]+" "$log" | head -1 | sed -E 's/.*:([0-9]+),.*/\1/')"
  if [ -z "$invalid_line" ] || [ -z "$diag_line" ] || [ "$diag_line" -lt "$invalid_line" ] ||
    ! grep -q 'when checking that' "$log" ||
    grep -Eq 'Not in scope|Failed to find|Unsolved|Parse error' "$log"; then
    cat "$log"
    echo "unexpected failure while checking $name"
    return 1
  fi
  return 0
}

shopt -s nullglob
accepts=(tests/accept/*.agda)
rejects=(tests/reject/*.agda)
shopt -u nullglob
if (( ${#accepts[@]} == 0 || ${#rejects[@]} == 0 )); then
  echo 'ERROR: tests/accept and tests/reject must each hold at least one module' >&2
  exit 1
fi

# 4. Positive controls.
for file in "${accepts[@]}"; do
  "$prover" "${flags[@]}" -i tests/accept "$file"
  echo "PASS: accepted $(basename -- "$file" .agda)"
done

# 5. Expected rejections.
for file in "${rejects[@]}"; do
  if ! expect_rejected "$file"; then
    echo "ERROR: $(basename -- "$file" .agda) was not rejected at its invalid declaration" >&2
    exit 1
  fi
  echo "PASS: rejected $(basename -- "$file" .agda) at its invalid declaration"
done

# 6. Negative control for step 5.
for file in "${accepts[@]}"; do
  if expect_rejected "$file" >/dev/null; then
    echo "ERROR: the rejection check reported positive control $(basename -- "$file" .agda) as rejected" >&2
    exit 1
  fi
  echo "PASS: rejection check reports positive control $(basename -- "$file" .agda) as accepted"
done

echo "PASS: Lintel proofs, ${#accepts[@]} positive control(s), ${#rejects[@]} expected rejection(s), negative control"
