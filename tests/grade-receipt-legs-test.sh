#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# Exercise the new legs receipt against an isolated, synthetic sibling tree.
set -euo pipefail
root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
fixture="$(mktemp -d)"
trap 'rm -rf "$fixture"' EXIT
mkdir -p "$fixture/scripts" "$fixture/verification" "$fixture/src/Lintel" \
  "$fixture/tests/accept" "$fixture/tests/reject" "$fixture/dependencies/secret-types/src"
cp "$root/scripts/"{grade-receipt,proof-flags,fetch-siblings,check-legs}.sh "$fixture/scripts/"
cp "$root/README.adoc" "$fixture/"
cp -R "$root/verification/legs" "$fixture/verification/"
printf 'module Lintel.All where\nimport SecretTypes\n' > "$fixture/src/Lintel/All.agda"
printf 'module SecretTypes where\n' > "$fixture/dependencies/secret-types/src/SecretTypes.agda"
# The receipt hashes sibling inputs without invoking a prover. Deliberately
# distinct contents make accidentally hashing Lintel's files detectable.
sibling_files=(verification/legs/rocq/SecretTypes.v verification/legs/lean/SecretTypes/Generic.lean
  verification/legs/lean/lakefile.toml verification/legs/lean/lean-toolchain)
for file in "${sibling_files[@]}"; do
  mkdir -p "$fixture/dependencies/secret-types/$(dirname "$file")"
  printf 'synthetic sibling input: %s\n' "$file" > "$fixture/dependencies/secret-types/$file"
done
export DEPENDENCIES_DIR="$fixture/dependencies" SECRET_TYPES_SRC="$fixture/dependencies/secret-types/src"
receipt="$fixture/verification/receipts/agda-pwg_praxis.deed"
check() {
  local expected="$1" diagnostic="$2" status=0
  shift 2
  bash "$fixture/scripts/grade-receipt.sh" "$@" > "$fixture/output" 2>&1 || status=$?
  if [[ "$status" != "$expected" ]] || ! grep -qF "$diagnostic" "$fixture/output"; then
    cat "$fixture/output" >&2
    echo "FAIL: $diagnostic (expected $expected, got $status)" >&2
    exit 1
  fi
  echo "PASS: $diagnostic"
}
write_receipt() { check 0 WROTE --write --commit aaaaaaaaaaaa; }
check_receipt() { check 0 'PASS: verification receipt matches the tree' --check --commit bbbbbbbbbbbb; }
write_receipt
check_receipt # Parent revision is intentionally ignored by --check.
cp "$receipt" "$fixture/first-receipt"
write_receipt
cmp "$receipt" "$fixture/first-receipt"
grep -qF ':prover "rocq" :checker "coqc" :version "8.18.0"' "$receipt"
grep -qF ':prover "lean" :checker "lean" :version "4.24.0"' "$receipt"
grep -qxF '    :state "RECONCILED"' "$receipt"
for id in L-1 L-2 L-3 L-4 L-6 L-7; do
  grep -qxF "    (claim :id \"$id\" :token \"proven\" :pwg \"2ii\" :coq-leg \"re-proved\" :lean-leg \"re-proved\")" "$receipt"
done
for row in 'L-5 tested-only' 'A-1 argued'; do
  read -r id token <<< "$row"
  grep -qxF "    (claim :id \"$id\" :token \"$token\" :pwg \"n/a\" :coq-leg \"n/a\" :lean-leg \"n/a\")" "$receipt"
done
# Independently enumerate all local inputs, checking exact hashes and that
# each appears once. Sorted output must not depend on filesystem order.
mapfile -t own_files < <(cd "$fixture" && find verification/legs -type f \
  \( -name '*.v' -o -name '*.lean' -o -name lakefile.toml -o -name lean-toolchain \) | LC_ALL=C sort)
for file in "${own_files[@]}"; do
  hash="$(sha256sum "$fixture/$file" | cut -d' ' -f1)"
  [[ "$(grep -cxF "      (input :path \"$file\" :sha256 \"$hash\")" "$receipt")" == 1 ]]
done
for file in "${sibling_files[@]}"; do
  hash="$(sha256sum "$fixture/dependencies/secret-types/$file" | cut -d' ' -f1)"
  [[ "$(grep -cxF "      (input :repository \"hyperpolymath/secret-types\" :path \"$file\" :sha256 \"$hash\")" "$receipt")" == 1 ]]
done
[[ "$(grep -c '^      (input ' "$receipt")" == $((${#own_files[@]} + ${#sibling_files[@]})) ]]
# Build caches are deliberately excluded from source hashing.
mkdir -p "$fixture/verification/legs/lean/.lake/packages/example"
echo 'generated build artifact' > "$fixture/verification/legs/lean/.lake/packages/example/Generated.lean"
check_receipt
# Every category of local and sibling input must invalidate a stale receipt.
for file in "${own_files[@]}"; do
  cp "$fixture/$file" "$fixture/saved"
  printf '\n-- changed input\n' >> "$fixture/$file"
  check 1 'ERROR: verification receipt does not match the tree' --check --commit bbbbbbbbbbbb
  cp "$fixture/saved" "$fixture/$file"
done
for file in "${sibling_files[@]}"; do
  cp "$fixture/dependencies/secret-types/$file" "$fixture/saved"
  echo 'changed sibling input' >> "$fixture/dependencies/secret-types/$file"
  check 1 'ERROR: verification receipt does not match the tree' --check --commit bbbbbbbbbbbb
  cp "$fixture/saved" "$fixture/dependencies/secret-types/$file"
  mv "$fixture/dependencies/secret-types/$file" "$fixture/missing"
  check 1 'ERROR: sibling leg file' --check --commit bbbbbbbbbbbb
  mv "$fixture/missing" "$fixture/dependencies/secret-types/$file"
done
# Checker pins are derived from the gate, not independently hard-coded.
sed -i 's/^COQ_VERSION=.*/COQ_VERSION=8.19.0/; s/^LEAN_VERSION=.*/LEAN_VERSION=4.25.0/' "$fixture/scripts/check-legs.sh"
check 1 'ERROR: verification receipt does not match the tree' --check --commit bbbbbbbbbbbb
write_receipt
grep -qF ':prover "rocq" :checker "coqc" :version "8.19.0"' "$receipt"
grep -qF ':prover "lean" :checker "lean" :version "4.25.0"' "$receipt"
check_receipt
# Cross-check correspondence rows in both directions. Repeated rows are
# legitimate: a claim may map to more than one theorem.
record="$fixture/verification/legs/README.adoc"
cp "$record" "$fixture/record"
printf '\n| L-1\n' >> "$record"
check_receipt
for id in L-1 L-2 L-3 L-4 L-6 L-7; do
  sed "/^| $id$/d" "$fixture/record" > "$record"
  check 1 'ERROR: claims with a counted leg differ' --check --commit bbbbbbbbbbbb
  grep -qF "only in grade-receipt.sh: $id" "$fixture/output"
done
for id in L-5 A-1 L-99; do
  cp "$fixture/record" "$record"
  printf '\n| %s\n' "$id" >> "$record"
  check 1 'ERROR: claims with a counted leg differ' --check --commit bbbbbbbbbbbb
  grep -qF "only in verification/legs/README.adoc: $id" "$fixture/output"
done
rm "$record"
check 1 'ERROR: claims with a counted leg differ' --check --commit bbbbbbbbbbbb
cp "$fixture/record" "$record"
check_receipt
