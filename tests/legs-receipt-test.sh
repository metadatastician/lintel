#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
set -euo pipefail
root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
fixture="$(mktemp -d)"
trap 'rm -rf "$fixture"' EXIT
mkdir -p "$fixture/scripts" "$fixture/src/Lintel" "$fixture/tests/accept" "$fixture/tests/reject" "$fixture/bin"
cp "$root/scripts/"{check-legs,grade-receipt,proof-flags,fetch-siblings}.sh "$fixture/scripts/"
mkdir -p "$fixture/docs/status" "$fixture/verification"
cp "$root/docs/status/PROOF-STATUS.adoc" "$fixture/docs/status/"
cp -R "$root/verification/legs" "$fixture/verification/"
sibling="$fixture/_build/dependencies/secret-types"
mkdir -p "$sibling/verification/legs/rocq" "$sibling/verification/legs/lean/SecretTypes"
touch "$sibling/verification/legs/rocq/SecretTypes.v" "$sibling/verification/legs/lean/SecretTypes/Generic.lean" \
  "$sibling/verification/legs/lean/lean-toolchain" "$sibling/verification/legs/lean/lakefile.toml"

# The receipt's cross-checks run in the shared generator (standards'
# scripts/proof-receipt.sh, tested there).  What is Lintel's are the hooks they
# read: the claim ids of the proof-status table and the claims whose two legs
# the legs record lists as RECONCILED.  Sourcing grade-receipt.sh defines them
# and runs nothing.
hooks() { (cd "$fixture" && . scripts/grade-receipt.sh && "$@"); }
theorems="$(hooks receipt_claims | awk -F'|' '$3=="theorem"{print $1}' | sort | paste -sd' ')"
[ "$(hooks receipt_recorded_legs | sort | paste -sd' ')" = "$theorems" ]
echo "PASS: the legs record lists both legs RECONCILED for exactly the theorems ($theorems)"
[ "$(hooks receipt_status_ids | sort | paste -sd' ')" = "$(hooks receipt_claims | cut -d'|' -f1 | sort | paste -sd' ')" ]
echo "PASS: the proof-status table names exactly the claims of the ledger"
for leg in rocq lean; do
  if [ "$leg" = rocq ]; then
    sed 's/| L-1 | RECONCILED | RECONCILED/| L-1 | PENDING | RECONCILED/' "$root/verification/legs/README.adoc" > "$fixture/verification/legs/README.adoc"
  else
    sed 's/| L-1 | RECONCILED | RECONCILED/| L-1 | RECONCILED | PENDING/' "$root/verification/legs/README.adoc" > "$fixture/verification/legs/README.adoc"
  fi
  ! hooks receipt_recorded_legs | grep -qx 'L-1'
  echo "PASS: a pending $leg correspondence drops L-1 from the recorded legs"
done
cp "$root/verification/legs/README.adoc" "$fixture/verification/legs/README.adoc"
printf '\n| L-1 | RECONCILED | PENDING\n' >> "$fixture/verification/legs/README.adoc"
! hooks receipt_recorded_legs | grep -qx 'L-1'
echo "PASS: a second row for L-1 that disagrees drops it too"
cp "$root/verification/legs/README.adoc" "$fixture/verification/legs/README.adoc"
rm "$fixture/verification/legs/README.adoc"
status=0; hooks receipt_recorded_legs > /dev/null 2>&1 || status=$?
[ "$status" -eq 3 ]
echo "PASS: a missing legs record is a hook refusal, not an empty list"
cp "$root/verification/legs/README.adoc" "$fixture/verification/legs/README.adoc"

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
