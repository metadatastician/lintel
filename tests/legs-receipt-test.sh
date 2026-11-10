#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
set -euo pipefail
root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
fixture="$(mktemp -d)"
trap 'rm -rf "$fixture"' EXIT
mkdir -p "$fixture/scripts" "$fixture/src/Lintel" "$fixture/tests/accept" "$fixture/tests/reject" "$fixture/bin"
cp "$root/scripts/"{check-legs,grade-receipt,proof-flags,fetch-siblings}.sh "$fixture/scripts/"
cp "$root/README.adoc" "$fixture/"
mkdir -p "$fixture/verification"
cp -R "$root/verification/legs" "$fixture/verification/"
sibling="$fixture/_build/dependencies/secret-types"
mkdir -p "$sibling/src" "$sibling/verification/legs/rocq" "$sibling/verification/legs/lean/SecretTypes"
mkdir -p "$sibling/src/SecretTypes"
printf "import SecretTypes.Prelude\n" > "$fixture/src/Lintel/All.agda"
touch "$sibling/src/SecretTypes/Prelude.agda" "$sibling/verification/legs/rocq/SecretTypes.v" \
  "$sibling/verification/legs/lean/SecretTypes/Generic.lean" \
  "$sibling/verification/legs/lean/lean-toolchain" "$sibling/verification/legs/lean/lakefile.toml"

# A baseline receipt can be generated, but neither pending leg may overwrite it.
bash "$fixture/scripts/grade-receipt.sh" --write > /dev/null
receipt="$fixture/verification/receipts/agda-pwg_praxis.deed"
cp "$receipt" "$fixture/baseline"
for leg in rocq lean; do
  if [ "$leg" = rocq ]; then
    sed 's/| L-1 | RECONCILED | RECONCILED/| L-1 | PENDING | RECONCILED/' "$root/verification/legs/README.adoc" > "$fixture/verification/legs/README.adoc"
  else
    sed 's/| L-1 | RECONCILED | RECONCILED/| L-1 | RECONCILED | PENDING/' "$root/verification/legs/README.adoc" > "$fixture/verification/legs/README.adoc"
  fi
  status=0
  bash "$fixture/scripts/grade-receipt.sh" --write > "$fixture/output" 2>&1 || status=$?
  [ "$status" -eq 1 ]
  grep -q 'counted legs must match RECONCILED states' "$fixture/output"
  cmp "$receipt" "$fixture/baseline"
  echo "PASS: pending $leg correspondence rejects receipt generation"
done

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
