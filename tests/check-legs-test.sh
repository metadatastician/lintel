#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# Unit tests of the gate, not substitutes for kernel-checking the proofs.
set -euo pipefail
root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
fixture="$(mktemp -d)"
trap 'rm -rf "$fixture"' EXIT
mkdir -p "$fixture/scripts" "$fixture/bin" "$fixture/_build/dependencies/secret-types/verification/legs/rocq" \
  "$fixture/_build/dependencies/secret-types/verification/legs/lean"
cp "$root/scripts/check-legs.sh" "$fixture/scripts/"
cp -R "$root/verification/legs" "$fixture/baseline"
# Minimal sibling sentinels: no network and no real compiler required.
touch "$fixture/_build/dependencies/secret-types/verification/legs/rocq/SecretTypes.v" \
  "$fixture/_build/dependencies/secret-types/verification/legs/lean/lakefile.toml"
cat > "$fixture/bin/coqc" <<'MOCK'
#!/usr/bin/env bash
set -euo pipefail
if [[ "$1" == --version ]]; then
  echo "The Coq Proof Assistant, version ${TEST_COQ_VERSION:-8.18.0}"
  exit 0
fi
printf 'coqc %s\n' "$*" >> "$TEST_CALLS"
if [[ "${*: -1}" == SecretTypes.v ]]; then
  exit "${TEST_SIBLING_STATUS:-0}"
fi
[[ "$*" == '-q -Q ../../../_build/dependencies/secret-types/verification/legs/rocq SecretTypesLeg Lintel.v' ]]
cat "$TEST_ROCQ_OUTPUT"
exit "${TEST_ROCQ_STATUS:-0}"
MOCK
cat > "$fixture/bin/lean" <<'MOCK'
#!/usr/bin/env bash
[[ "$*" == --version ]] || exit 99
echo "Lean (version ${TEST_LEAN_VERSION:-4.24.0}, test)"
MOCK
cat > "$fixture/bin/lake" <<'MOCK'
#!/usr/bin/env bash
set -euo pipefail
printf 'lake %s\n' "$*" >> "$TEST_CALLS"
case "$*" in
  build) exit "${TEST_BUILD_STATUS:-0}" ;;
  'env lean Axioms.lean') cat "$TEST_LEAN_OUTPUT"; exit "${TEST_LEAN_STATUS:-0}" ;;
  *) exit 99 ;;
esac
MOCK
chmod +x "$fixture/bin/"*
export PATH="$fixture/bin:$PATH" TEST_CALLS="$fixture/calls" \
  TEST_ROCQ_OUTPUT="$fixture/rocq-output" TEST_LEAN_OUTPUT="$fixture/lean-output"
reset_case() {
  rm -rf "$fixture/verification"
  mkdir -p "$fixture/verification"
  cp -R "$fixture/baseline" "$fixture/verification/legs"
  unset TEST_COQ_VERSION TEST_LEAN_VERSION TEST_SIBLING_STATUS TEST_ROCQ_STATUS TEST_BUILD_STATUS TEST_LEAN_STATUS
  : > "$TEST_CALLS"
  # Generate normal diagnostics from the actual statement lists, so added
  # statements are automatically exercised rather than tied to a magic count.
  sed -n 's/^Print Assumptions .*/Closed under the global context/p' \
    "$fixture/verification/legs/rocq/Lintel.v" > "$TEST_ROCQ_OUTPUT"
  sed -n "s/^#print axioms \(.*\)/'\1' does not depend on any axioms/p" \
    "$fixture/verification/legs/lean/Axioms.lean" > "$TEST_LEAN_OUTPUT"
}
check() {
  local expected="$1" diagnostic="$2" status=0
  bash "$fixture/scripts/check-legs.sh" > "$fixture/output" 2>&1 || status=$?
  if [[ "$status" != "$expected" ]] || ! grep -qF "$diagnostic" "$fixture/output"; then
    cat "$fixture/output" >&2
    echo "FAIL: $diagnostic (expected $expected, got $status)" >&2
    exit 1
  fi
  echo "PASS: $diagnostic"
}
reset_case
check 0 'PASS: both recheck legs'
[[ "$(wc -l < "$TEST_CALLS")" == 4 ]]
grep -qxF 'coqc -q -Q . SecretTypesLeg SecretTypes.v' "$TEST_CALLS"
grep -qxF 'lake build' "$TEST_CALLS"
grep -qxF 'lake env lean Axioms.lean' "$TEST_CALLS"
for tool in COQ LEAN; do
  reset_case
  export "TEST_${tool}_VERSION=0.0.0"
  check 2 'ERROR: expected'
  [[ ! -s "$TEST_CALLS" ]]
done
for file in rocq/SecretTypes.v lean/lakefile.toml; do
  sentinel="$fixture/_build/dependencies/secret-types/verification/legs/$file"
  reset_case
  mv "$sentinel" "$sentinel.saved"
  check 2 'legs not found'
  [[ ! -s "$TEST_CALLS" ]]
  mv "$sentinel.saved" "$sentinel"
done
reset_case
printf '\n[[require]]\nname = "mathlib"\n' >> "$fixture/verification/legs/lean/lakefile.toml"
check 1 'FAIL: the Lean leg may depend'
reset_case
sed -i 's|../../../_build/dependencies|/untrusted|' "$fixture/verification/legs/lean/lakefile.toml"
check 1 'FAIL: the Lean leg may depend'
for key in git rev scope source; do
  reset_case
  printf '\n%s = "untrusted"\n' "$key" >> "$fixture/verification/legs/lean/lakefile.toml"
  check 1 'FAIL: the Lean leg may depend'
done
reset_case
printf '\nFrom Coq Require Import Bool.\n' >> "$fixture/verification/legs/rocq/Lintel.v"
check 1 'FAIL: the Rocq leg may load'
for word in sorry admit Admitted Axiom Parameter axiom; do
  for file in rocq/Lintel.v lean/Lintel/Lattice.lean lean/Lintel.lean; do
    reset_case
    printf '\n%s\n' "$word" >> "$fixture/verification/legs/$file"
    check 1 'FAIL: an escape hatch in a leg'
  done
done
for leg in ROCQ LEAN; do
  for corruption in missing extra axiom noise empty; do
    reset_case
    output_var="TEST_${leg}_OUTPUT"
    output="${!output_var}"
    case "$corruption" in
      missing) sed -i '$d' "$output" ;;
      extra) head -n 1 "$output" >> "$output.extra"; cat "$output.extra" >> "$output" ;;
      axiom) sed -i '1c depends on axioms: unsafe' "$output" ;;
      noise) echo 'unexpected diagnostic' >> "$output" ;;
      empty) : > "$output" ;;
    esac
    check 1 'rests on an axiom'
  done
done
for stage in SIBLING ROCQ BUILD LEAN; do
  reset_case
  export "TEST_${stage}_STATUS=17"
  check 1 'does not check'
  if [[ "$stage" == SIBLING || "$stage" == ROCQ ]]; then
    if grep -q '^lake ' "$TEST_CALLS"; then exit 1; fi
  elif [[ "$stage" == BUILD ]]; then
    if grep -q '^lake env ' "$TEST_CALLS"; then exit 1; fi
  fi
done
