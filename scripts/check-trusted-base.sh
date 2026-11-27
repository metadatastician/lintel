#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
#
# check-trusted-base.sh: the prover's trusted base and the Agda input set of
# the receipt, against what Agda itself reports (PROOF-POLICY §8.4, §8.5.1).
# Pattern: hyperpolymath/secret-types scripts/check-trusted-base.sh.
#
# The import cone of src/Lintel/All.agda includes modules that Agda supplies,
# such as Agda.Primitive.  Some declare primitives by postulate, and --safe
# accepts them.  Such a postulate is admissible only if the receipt lists it by
# name with its binding, and the gate checks that exact list.  This script:
#   1. runs the scanner's controls (tests/trusted-base), so a scanner that
#      stops finding postulates fails here first;
#   2. asks Agda for the cone (--dependency-graph, under the gate's flags), and
#      requires the receipt's Agda input set to be exactly that cone: the
#      Lintel modules of `grade-receipt.sh --inputs agda`, and the
#      secret-types modules of `grade-receipt.sh --sibling-cone` (its imports);
#   3. scans every prover-supplied module of the cone for postulates;
#   4. requires the result to be exactly proof_trusted_base
#      (scripts/proof-flags.sh), which the receipt writes as (trusted-base ...).
# Any difference fails.  A prover pin bump that changes the list fails here
# until proof_trusted_base is updated and the receipt is earned again.
#
# Needs agda (the pinned version), the secret-types checkout
# (scripts/fetch-siblings.sh) and the pinned standards files
# (scripts/grade-receipt.sh --fetch-standards).
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.."
export LC_ALL=C
. scripts/proof-flags.sh
prover="${AGDA:-agda}"
st="${SECRET_TYPES_SRC:-${DEPENDENCIES_DIR:-_build/dependencies}/secret-types/src}"
root=src/Lintel/All.agda
scan=scripts/scan-agda-postulates.awk
work="$(mktemp -d)"; trap 'rm -rf "$work"' EXIT
[[ -d "$st" ]] || { echo "ERROR: secret-types sources not found at $st (run scripts/fetch-siblings.sh)" >&2; exit 1; }

# 1. Controls.  Positive and comment-only fixtures must give their expected
# lists; the refusal fixtures must be refused (exit 3), never passed.  Two
# refusal controls carry control bytes, which the estate's invisible-character
# scan refuses in the tree (and .gitattributes would normalise CRLF), so they
# are stored without them and get them here; each must then be refused for
# that byte, since its postulate alone would be refused too.
ff="$(printf '\f')"
declare -A reason=([CarriageReturn]='carriage return' [FormFeed]='form feed')
for f in tests/trusted-base/*.txt; do
  name="$(basename -- "$f" .txt)"
  case "$name" in
    CarriageReturn)
      sed 's/$/\r/' "$f" > "$work/$name.ctl"
      grep -q $'\r' "$work/$name.ctl" || { echo 'FAIL: could not build the CRLF control' >&2; exit 1; }
      f="$work/$name.ctl" ;;
    FormFeed)
      sed "s/^postulate Hidden/postulate${ff}Hidden/" "$f" > "$work/$name.ctl"
      grep -q "$ff" "$work/$name.ctl" || { echo 'FAIL: could not build the form-feed control' >&2; exit 1; }
      f="$work/$name.ctl" ;;
  esac
  set +e; awk -v "module=Fixture.$name" -f "$scan" "$f" > "$work/$name.out" 2> "$work/$name.err"; rc=$?; set -e
  if [[ -f "tests/trusted-base/$name.expected" ]]; then
    if (( rc != 0 )) || ! diff -u "tests/trusted-base/$name.expected" "$work/$name.out"; then
      cat "$work/$name.err" >&2
      echo "FAIL: scanner control $name (rc=$rc)" >&2; exit 1
    fi
  elif (( rc != 3 )); then
    cat "$work/$name.out" >&2
    echo "FAIL: scanner control $name was not refused (rc=$rc)" >&2; exit 1
  fi
  if [[ -n "${reason[$name]:-}" ]] && ! grep -q "${reason[$name]}" "$work/$name.err"; then
    cat "$work/$name.err" >&2
    echo "FAIL: scanner control $name was refused, but not for its ${reason[$name]}" >&2; exit 1
  fi
done
echo "PASS: scanner controls ($(ls tests/trusted-base/*.txt | wc -l | tr -d ' ') fixtures)"

# 2. The cone, as Agda reports it under the gate's flags.
mapfile -t flags < <(proof_flags)
"$prover" "${flags[@]}" -i src -i "$st" --dependency-graph="$work/cone.dot" "$root" > "$work/agda.log" 2>&1 \
  || { cat "$work/agda.log" >&2; echo 'FAIL: agda could not produce the dependency graph' >&2; exit 1; }
mapfile -t cone < <(sed -n 's/.*label="\([^"]*\)".*/\1/p' "$work/cone.dot" | sort -u)
(( ${#cone[@]} > 0 )) || { echo 'FAIL: empty dependency graph' >&2; exit 1; }
agda_dir="$("$prover" --print-agda-dir)"

# The receipt's Agda input set, from the hooks the receipt is written with.
bash scripts/grade-receipt.sh --inputs agda | grep -E '\.agda$' | sort > "$work/scan-home" \
  || { echo 'FAIL: grade-receipt.sh --inputs agda failed' >&2; exit 1; }
bash scripts/grade-receipt.sh --sibling-cone | sort > "$work/scan-import" \
  || { echo 'FAIL: grade-receipt.sh --sibling-cone failed' >&2; exit 1; }
: > "$work/cone-home"; : > "$work/cone-import"
for m in "${cone[@]}"; do
  rel="${m//.//}.agda"
  if [[ -f "src/$rel" ]]; then printf 'src/%s\n' "$rel" >> "$work/cone-home"
  elif [[ -f "$st/$rel" ]]; then printf 'src/%s\n' "$rel" >> "$work/cone-import"; fi
done
sort -o "$work/cone-home" "$work/cone-home"; sort -o "$work/cone-import" "$work/cone-import"
for part in home import; do
  if ! diff -u "$work/cone-$part" "$work/scan-$part"; then
    echo "FAIL: the receipt's Agda input set ($part) differs from the cone agda --dependency-graph reports" >&2
    exit 1
  fi
done
echo "PASS: the receipt's Agda input set equals the cone Agda reports ($(wc -l < "$work/cone-home" | tr -d ' ') Lintel, $(wc -l < "$work/cone-import" | tr -d ' ') secret-types modules)"

# 3. Scan the prover-supplied modules.  Every module of the cone is Lintel's,
# the sibling's, or Agda's (under the prover's lib/prim); a module in none of
# them fails, so nothing in the cone goes unscanned.
supplied=0
: > "$work/found"
for m in "${cone[@]}"; do
  rel="${m//.//}.agda"
  if [[ -f "src/$rel" || -f "$st/$rel" ]]; then continue; fi
  path="$agda_dir/lib/prim/$rel"
  [[ -f "$path" ]] || { echo "FAIL: module $m of the cone is in neither src/, the sibling, nor $agda_dir/lib/prim" >&2; exit 1; }
  supplied=$((supplied + 1))
  awk -v "module=$m" -f "$scan" "$path" >> "$work/found"
done

# 4. Compare with proof_trusted_base, the list the receipt writes.
sort -u "$work/found" > "$work/found.sorted"
proof_trusted_base | sort -u > "$work/declared.sorted"
if ! diff -u "$work/declared.sorted" "$work/found.sorted"; then
  echo 'FAIL: the prover-supplied postulates of the cone differ from proof_trusted_base (scripts/proof-flags.sh)' >&2
  exit 1
fi
echo "PASS: trusted base: $(wc -l < "$work/found.sorted" | tr -d ' ') prover postulates in $supplied prover-supplied modules of the cone, each BUILTIN-bound and listed; no other postulate"
