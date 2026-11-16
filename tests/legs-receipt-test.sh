#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
set -euo pipefail
root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
fixture="$(mktemp -d)"
trap 'rm -rf "$fixture"' EXIT
mkdir -p "$fixture/scripts" "$fixture/src/Lintel" "$fixture/tests/accept" "$fixture/tests/reject" "$fixture/bin"
cp "$root/scripts/"{check-legs,grade-receipt,proof-flags,fetch-siblings}.sh "$fixture/scripts/"
cp "$root/README.adoc" "$fixture/"
mkdir -p "$fixture/verification/receipts"
cp -R "$root/verification/legs" "$fixture/verification/"
cp "$root/verification/receipts/agda-pwg_praxis.deed" "$fixture/verification/receipts/"
sibling="$fixture/_build/dependencies/secret-types"
mkdir -p "$sibling/verification/legs/rocq" "$sibling/verification/legs/lean/SecretTypes"
touch "$sibling/verification/legs/rocq/SecretTypes.v" "$sibling/verification/legs/lean/SecretTypes/Generic.lean" \
  "$sibling/verification/legs/lean/lean-toolchain" "$sibling/verification/legs/lean/lakefile.toml"

# The committed receipt agrees with README.adoc and the legs record; a leg
# whose correspondence is not RECONCILED, or a claim missing from either side,
# fails the cross-check.
bash "$fixture/scripts/grade-receipt.sh" --cross-check > /dev/null
echo "PASS: the receipt's claims and legs match the human records"
for leg in rocq lean; do
  if [ "$leg" = rocq ]; then
    sed 's/| L-1 | RECONCILED | RECONCILED/| L-1 | PENDING | RECONCILED/' "$root/verification/legs/README.adoc" > "$fixture/verification/legs/README.adoc"
  else
    sed 's/| L-1 | RECONCILED | RECONCILED/| L-1 | RECONCILED | PENDING/' "$root/verification/legs/README.adoc" > "$fixture/verification/legs/README.adoc"
  fi
  status=0
  bash "$fixture/scripts/grade-receipt.sh" --cross-check > "$fixture/output" 2>&1 || status=$?
  [ "$status" -eq 1 ]
  grep -q "the receipt's legs and their states must be the rows" "$fixture/output"
  grep -q "L-1|$leg|PENDING" "$fixture/output"
  echo "PASS: a pending $leg correspondence fails the receipt cross-check"
done
cp "$root/verification/legs/README.adoc" "$fixture/verification/legs/README.adoc"
sed 's/^| L-7$/| L-8/' "$root/README.adoc" > "$fixture/README.adoc"
status=0
bash "$fixture/scripts/grade-receipt.sh" --cross-check > "$fixture/output" 2>&1 || status=$?
[ "$status" -eq 1 ]
grep -q 'claim ids differ between the receipt and README.adoc' "$fixture/output"
echo "PASS: a claim missing from the receipt fails the cross-check"
cp "$root/README.adoc" "$fixture/"

# Fake checkers exercise orchestration and diagnostics, not proof correctness.
cat > "$fixture/bin/coqc" <<'COQ'
#!/usr/bin/env bash
if [ "$1" = --version ]; then
  echo 'The Coq Proof Assistant, version 8.18.0'
elif [ "${*: -1}" = Lintel.v ]; then
  grep '^Print Assumptions ' Lintel.v | sed 's/.*/Closed under the global context/'
fi
COQ
cat > "$fixture/bin/lean" <<'LEAN'
#!/usr/bin/env bash
echo 'Lean (version 4.24.0, fixture)'
LEAN
cat > "$fixture/bin/lake" <<'LAKE'
#!/usr/bin/env bash
if [ "$1" = build ]; then
  echo build-stdout
  echo build-stderr >&2
  [ "$CASE" != build-failure ]
else
  touch "$MARKER"
  if [ "$CASE" = axiom-failure ]; then
    echo axiom-stdout
    echo axiom-stderr >&2
    exit 1
  elif [ "$CASE" = axiom-present ]; then
    echo 'statement depends on axioms: [fixture]'
  else
    grep '^#print axioms ' Axioms.lean | sed 's/.*/does not depend on any axioms/'
  fi
fi
LAKE
chmod +x "$fixture/bin/"*
for scenario in build-failure axiom-failure axiom-present success; do
  rm -f "$fixture/axiom-ran"
  status=0
  PATH="$fixture/bin:$PATH" CASE="$scenario" MARKER="$fixture/axiom-ran" \
    bash "$fixture/scripts/check-legs.sh" > "$fixture/output" 2>&1 || status=$?
  case "$scenario" in
    build-failure)
      [ "$status" -eq 1 ]; [ ! -f "$fixture/axiom-ran" ]
      grep -q build-stdout "$fixture/output"
      grep -q build-stderr "$fixture/output"
      grep -q 'FAIL: the Lean leg does not build' "$fixture/output" ;;
    axiom-failure)
      [ "$status" -eq 1 ]; [ -f "$fixture/axiom-ran" ]
      grep -q axiom-stdout "$fixture/output"
      grep -q axiom-stderr "$fixture/output"
      grep -q 'FAIL: the Lean leg does not check' "$fixture/output"
      ! grep -q build-stdout "$fixture/output" ;;
    axiom-present)
      [ "$status" -eq 1 ]
      grep -q 'FAIL: the Lean leg rests on an axiom' "$fixture/output" ;;
    success)
      [ "$status" -eq 0 ]
      grep -q 'PASS: both recheck legs' "$fixture/output" ;;
  esac
  echo "PASS: Lean $scenario"
done
