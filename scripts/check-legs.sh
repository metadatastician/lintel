#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
#
# check-legs.sh: the Rocq and Lean recheck legs (PROOF-POLICY §2) of
# L-1, L-2, L-3, L-4, L-6 and L-7.  Run scripts/fetch-siblings.sh first.
#
# Lintel's legs build on secret-types' own legs at the pin, as the Agda gate
# builds on secret-types' Agda sources at the pin: the record, the language,
# the typing rules and TINI are imported, never restated.  So each leg is
# allowed exactly one dependency, and nothing else:
#   * Lean: one `[[require]]`, secret-types' Lean leg in the pinned checkout;
#     no Mathlib, no other package;
#   * Rocq: `Require SecretTypesLeg.SecretTypes.` (secret-types' Rocq leg in
#     the pinned checkout) and its coercions; no standard library.
# Then it refuses any axiom.  `Print Assumptions` and `#print axioms` are
# transitive, so an axiom anywhere in secret-types' legs would show here too:
#   * every `Print Assumptions` line must read "Closed under the global context";
#   * every `#print axioms` line must read "does not depend on any axioms".
#
# Pins: COQ_VERSION and LEAN_VERSION below, fixed (no environment override);
# scripts/grade-receipt.sh reads them from here into the receipt.
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.."
export LC_ALL="${LC_ALL:-C.UTF-8}"

COQ_VERSION=8.18.0
LEAN_VERSION=4.24.0
fail=0

# The Lean lakefile names the sibling by this path, so it is not overridable.
sibling=_build/dependencies/secret-types/verification/legs
if [ ! -f "$sibling/rocq/SecretTypes.v" ] || [ ! -f "$sibling/lean/lakefile.toml" ]; then
  echo "ERROR: secret-types' legs not found under $sibling (run scripts/fetch-siblings.sh)" >&2
  exit 2
fi

got="$(coqc --version | sed -n 's/^The Coq Proof Assistant, version \([0-9.]*\).*/\1/p')"
[ "$got" = "$COQ_VERSION" ] || { echo "ERROR: expected Coq $COQ_VERSION, found '${got:-none}'" >&2; exit 2; }
got="$(lean --version | sed -n 's/^Lean (version \([0-9.]*\),.*/\1/p')"
[ "$got" = "$LEAN_VERSION" ] || { echo "ERROR: expected Lean $LEAN_VERSION, found '${got:-none}'" >&2; exit 2; }

# Lean: exactly one require, and it is the pinned sibling's leg.
lakefile=verification/legs/lean/lakefile.toml
n_req="$(grep -cE '^\s*\[\[require\]\]' "$lakefile" || true)"
if [ "$n_req" != 1 ] \
   || ! grep -qxF 'name = "secret-types-lean-leg"' "$lakefile" \
   || ! grep -qxF 'path = "../../../_build/dependencies/secret-types/verification/legs/lean"' "$lakefile" \
   || grep -nE '^\s*(git|rev|scope|source)\s*=|^\s*require\b' "$lakefile"; then
  echo "FAIL: the Lean leg may depend on secret-types' Lean leg at the pin, and on nothing else" >&2; fail=1
fi
# Rocq: the only loads are secret-types' leg and its coercions.
loads="$(grep -hE '^\s*(From\s+\S+\s+)?(Require|Import|Export)\b' verification/legs/rocq/*.v || true)"
want="$(printf '%s\n' 'Require SecretTypesLeg.SecretTypes.' 'Import (coercions) SecretTypesLeg.SecretTypes.')"
if [ "$loads" != "$want" ]; then
  printf '%s\n' "$loads" >&2
  echo "FAIL: the Rocq leg may load secret-types' Rocq leg and its coercions, and nothing else" >&2; fail=1
fi
# No escape hatches in either leg.
if grep -nE '\b(sorry|admit|Admitted|Axiom|Parameter|axiom)\b' \
     verification/legs/rocq/*.v verification/legs/lean/Lintel/*.lean verification/legs/lean/Lintel.lean; then
  echo 'FAIL: an escape hatch in a leg' >&2; fail=1
fi

# Rocq: compile secret-types' leg under the logical name, then Lintel's.
rocq_out="$( (cd "$sibling/rocq" && coqc -q -Q . SecretTypesLeg SecretTypes.v >/dev/null) 2>&1 \
  && cd verification/legs/rocq && coqc -q -Q "../../../$sibling/rocq" SecretTypesLeg Lintel.v 2>&1)" \
  || { echo "$rocq_out" >&2; echo 'FAIL: the Rocq leg does not check' >&2; exit 1; }
n_closed="$(grep -c '^Closed under the global context$' <<< "$rocq_out" || true)"
n_print="$(grep -c '^Print Assumptions ' verification/legs/rocq/Lintel.v)"
if [ "$n_closed" != "$n_print" ] || grep -vq '^Closed under the global context$' <<< "$rocq_out"; then
  echo "$rocq_out" >&2; echo "FAIL: the Rocq leg rests on an axiom ($n_closed of $n_print closed)" >&2; fail=1
else
  echo "PASS: Rocq leg (Coq $COQ_VERSION), $n_print statements closed under the global context"
fi

lean_out="$(cd verification/legs/lean && lake build >/dev/null && lake env lean Axioms.lean 2>&1)" \
  || { echo "$lean_out" >&2; echo 'FAIL: the Lean leg does not check' >&2; exit 1; }
n_free="$(grep -c 'does not depend on any axioms$' <<< "$lean_out" || true)"
n_ax="$(grep -c '^#print axioms ' verification/legs/lean/Axioms.lean)"
if [ "$n_free" != "$n_ax" ] || grep -vq 'does not depend on any axioms$' <<< "$lean_out"; then
  echo "$lean_out" >&2; echo "FAIL: the Lean leg rests on an axiom ($n_free of $n_ax free)" >&2; fail=1
else
  echo "PASS: Lean leg (Lean $LEAN_VERSION, core only), $n_ax statements depend on no axioms"
fi

(( fail == 0 )) || exit 1
echo 'PASS: both recheck legs'
