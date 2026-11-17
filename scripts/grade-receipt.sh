#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
#
# grade-receipt.sh: Lintel's proof receipt, verification/receipts/agda-pwg_praxis.deed,
# in the shape of PROOF-POLICY §8.5.1 to §8.5.3, written and checked by the
# shared generator of the standard (scripts/proof-receipt.sh, standards#1620).
# This file holds only what is Lintel's: the claim, run and echo ledgers and
# the hooks that name each leg's invocation and input set.
#
#   --fetch-standards    fetch the pinned standards files into _build/standards
#                        and check each one's sha256
#   --write              write the receipt from the tree and the ledgers
#   --check              regenerate it, refuse any difference, run the git
#                        checks of §8.5.3, check that each current receipt still
#                        describes the tree, and run the pinned reader with a
#                        negative control
#   --inputs PROVER      the §8.5.1 home input set of a leg
#   --sibling-cone       the secret-types modules of the Agda cone, as paths in
#                        that repository (scripts/check-trusted-base.sh reads it)
#   --run-row PROVER --run URL --commit SHA --checker TEXT --reported TEXT
#                        print the ledger row of a run that just passed
#
# Run scripts/fetch-siblings.sh first: the receipt imports secret-types at its
# pin, and the hooks read that checkout.
# Sourced (by tests), it defines the ledgers and hooks and runs nothing.
[[ "${BASH_SOURCE[0]}" != "$0" ]] || set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.."
export LC_ALL=C.UTF-8
. scripts/proof-flags.sh

# ── The pinned standard: four files at one commit, each with its sha256 ──────
STANDARDS_COMMIT=58362c24cf225694b388fc660b3525d8207b7c61
declare -A STANDARDS_FILES=(
  [scripts/proof-receipt.sh]=bfe35c08397ab85d7d33998ae126e189988994598320ffd2b139f2038e8eec4c
  [1-formats/deed/tools/deed_lint.js]=8978546740ca2d6a1d90b769fe02159883cb18f1eb2c44b2eeb737bab341dcd2
  [scripts/proof-inputs-sha256.sh]=dfc6dde01a3a79df638eebe4cad0eae584d8f17280077e149174c0667e9508f4
  [scripts/check-proof-receipt.sh]=f2375747238464535d1b4a61f658f07cb2f8504c69bfb1812311c79429a4e23e
)
STD=_build/standards
SIBLING=${DEPENDENCIES_DIR:-_build/dependencies}/secret-types
PIN_FILE=scripts/fetch-siblings.sh

die() { printf 'ERROR: %s\n' "$*" >&2; exit 1; }
fetch_standards() {
  local path sum dest
  for path in "${!STANDARDS_FILES[@]}"; do
    sum="${STANDARDS_FILES[$path]}" dest="$STD/$path"
    mkdir -p "$(dirname "$dest")"
    curl --proto '=https' --tlsv1.2 -fsSL \
      "https://raw.githubusercontent.com/metadatastician/standards/$STANDARDS_COMMIT/$path" -o "$dest.tmp"
    echo "$sum  $dest.tmp" | sha256sum --check --strict >/dev/null \
      || { rm -f "$dest.tmp"; die "the fetched $path does not match its pinned sha256"; }
    mv "$dest.tmp" "$dest"; printf 'FETCHED %s (standards %s)\n' "$path" "${STANDARDS_COMMIT:0:12}"
  done
}
check_standards() {
  local path
  for path in "${!STANDARDS_FILES[@]}"; do
    [[ -f "$STD/$path" ]] || die "the pinned $path is missing: run bash scripts/grade-receipt.sh --fetch-standards"
    [[ "$(sha256sum "$STD/$path" | cut -d' ' -f1)" == "${STANDARDS_FILES[$path]}" ]] \
      || die "$STD/$path is not the pinned file (sha256 differs)"
  done
}

RECEIPT_STD=$STD
RECEIPT_STANDARDS_COMMIT=$STANDARDS_COMMIT
RECEIPT_OUT=verification/receipts/agda-pwg_praxis.deed
RECEIPT_REPOSITORY=metadatastician/lintel
RECEIPT_DEFAULT_BRANCH=main
RECEIPT_CANONICAL_NAME=lintel-proof-receipt
RECEIPT_SCRIPT=scripts/grade-receipt.sh

# ── The claim list ────────────────────────────────────────────────────────────
# id | §5 token of the Agda proof | kind | Rocq route | Rocq §2.2 state |
# Lean route | Lean §2.2 state | Rocq reason | Lean reason.  Only theorems are
# graded (§8.1).  Both recheck legs are re-proved and RECONCILED in
# verification/legs/README.adoc.
receipt_claims() {
  cat <<'ROWS'
L-1|proven|theorem|re-proved|RECONCILED|re-proved|RECONCILED||
L-2|proven|theorem|re-proved|RECONCILED|re-proved|RECONCILED||
L-3|proven|theorem|re-proved|RECONCILED|re-proved|RECONCILED||
L-4|proven|theorem|re-proved|RECONCILED|re-proved|RECONCILED||
L-5|tested-only|demonstration|n/a|n/a|n/a|n/a||
L-6|proven|theorem|re-proved|RECONCILED|re-proved|RECONCILED||
L-7|proven|theorem|re-proved|RECONCILED|re-proved|RECONCILED||
A-1|argued|assumption|n/a|n/a|n/a|n/a||
ROWS
}

# ── The run ledger ────────────────────────────────────────────────────────────
# prover | run | commit | checker | invocation | inputs sha256 | reported |
# state | reason | axioms [| imports [| trusted base]].  A current row is
# printed by --run-row from the log of the run that passed; no row is typed.
# Run 42740256887 (on 89ceac3, main) checked the legs at the earlier
# secret-types pin; the re-pin to 9fb8430 changed every leg's inputs, so the
# first run on main after it is recorded next.  Until then nothing is graded.
receipt_runs() {
  cat <<'ROWS'
agda|https://github.com/metadatastician/lintel/actions/runs/42740256887/attempts/1|89ceac3b8685467c664737a98364eef4febb9ff2|Agda version 2.6.4.3 (Debian 13 agda-bin=2.6.4.3-1+b2, container debian:13-slim)|agda --safe --without-K --cubical-compatible --no-libraries --ignore-interfaces --double-check -W error -i src -i _build/dependencies/secret-types/src src/Lintel/All.agda|39a57e7d6ad052fd5dae5c3d1528ecb2121b9d7579c9f5517e0af7645e3a6194|PASS: Lintel proofs, 5 positive control(s), 4 expected rejection(s), negative control|superseded|the re-pin of secret-types from 45046c2 to 9fb8430 changed the inputs; the first run on main after it replaces this one|
rocq|https://github.com/metadatastician/lintel/actions/runs/42740256887/attempts/1|89ceac3b8685467c664737a98364eef4febb9ff2|Coq 8.18.0 (Ubuntu 24.04 coq=8.18.0+dfsg-1build2, bare runner)|coqc -q -Q . SecretTypesLeg SecretTypes.v (in the secret-types leg); coqc -q -Q ../../../_build/dependencies/secret-types/verification/legs/rocq SecretTypesLeg Lintel.v (in verification/legs/rocq)|71aa1f2cdfc11d1e4ac01538aea470d7991bbbd5f67db122693604bf735947e7|PASS: Rocq leg (Coq 8.18.0), 36 statements closed under the global context|superseded|the re-pin of secret-types from 45046c2 to 9fb8430 changed the inputs, and this run was on a bare runner (PROOF-POLICY 8.2 isolation); the first run on main in the pinned image replaces it|
lean|https://github.com/metadatastician/lintel/actions/runs/42740256887/attempts/1|89ceac3b8685467c664737a98364eef4febb9ff2|Lean 4.24.0 (release tarball, bare runner)|lake build; lake env lean Axioms.lean (in verification/legs/lean)|01ef18b09ee3a85365e2888d673f1490a5bc16489352f4ca8f155c6f8e60a914|PASS: Lean leg (Lean 4.24.0, core only), 36 statements depend on no axioms|superseded|the re-pin of secret-types from 45046c2 to 9fb8430 changed the inputs, and this run was on a bare runner (PROOF-POLICY 8.2 isolation); the first run on main in the pinned image replaces it|
ROWS
}

# ── The echo ledger (§8.5.2) ──────────────────────────────────────────────────
receipt_echoes() { :; }

receipt_header() {
  cat <<'HEAD'
;; SPDX-License-Identifier: CC-BY-SA-4.0
;; SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
;; The proof receipt of Lintel (PROOF-POLICY §8.5.1).
;; GENERATED by scripts/grade-receipt.sh with the shared generator of the
;; standard (scripts/proof-receipt.sh): regenerate with --write, check with --check.
;; L-5 (checked refusals) and A-1 (an assumption) are not theorems (§8.1).
;; The trusted base is what scripts/check-trusted-base.sh finds in the
;; prover-supplied modules of the import cone of src/Lintel/All.agda.
HEAD
}

receipt_trusted_base() { proof_trusted_base; }

receipt_invocation() {
  case "$1" in
    agda) printf 'agda %s -i src -i _build/dependencies/secret-types/src src/Lintel/All.agda\n' "$(proof_flags_line)" ;;
    rocq) printf '%s\n' 'coqc -q -Q . SecretTypesLeg SecretTypes.v (in the secret-types leg); coqc -q -Q ../../../_build/dependencies/secret-types/verification/legs/rocq SecretTypesLeg Lintel.v (in verification/legs/rocq)' ;;
    lean) printf '%s\n' 'lake build; lake env lean Axioms.lean (in verification/legs/lean)' ;;
  esac
}

# The home input set of each leg (§8.5.1).  The pin file is in each, because
# it fixes the imported files: a repin changes every leg's digest.
lean_files() { git -C "$1" ls-files -- verification/legs/lean | grep -E '(\.lean|/lakefile\.(lean|toml)|/lean-toolchain|/lake-manifest\.json)$'; }
receipt_inputs() {
  [[ -d "$SIBLING/src" ]] || return 3
  case "$1" in
    agda) receipt_agda_cone src/Lintel/All.agda src "$SIBLING/src" | grep -v "^$SIBLING/" ;;
    rocq) printf '%s\n' verification/legs/rocq/Lintel.v ;;
    lean) lean_files . ;;
  esac
  printf '%s\n' "$PIN_FILE"
}
# The files each leg read from secret-types at the pin its home commit names.
receipt_imports() {
  local pin
  pin="$(git show "$2:$PIN_FILE" | sed -nE 's/^SECRET_TYPES_COMMIT="\$\{SECRET_TYPES_COMMIT:-([0-9a-f]{40})\}"$/\1/p')"
  [[ "$pin" =~ ^[0-9a-f]{40}$ ]] || return 3
  case "$1" in
    agda) receipt_agda_cone src/Lintel/All.agda src "$SIBLING/src" | sed -n "s|^$SIBLING/||p" ;;
    rocq) printf '%s\n' verification/legs/rocq/SecretTypes.v ;;
    lean) lean_files "$SIBLING" ;;
  esac | while read -r p; do printf '%s|%s|%s|%s\n' hyperpolymath/secret-types "$pin" "$SIBLING" "$p"; done
}

# The claim ids of the proof-status table, and the ids whose two recheck legs
# the legs record lists as RECONCILED (a row with any other state drops out,
# so the gate fails on it).
receipt_status_ids() { grep -oE '^\| [LA]-[0-9]+ \|' docs/status/PROOF-STATUS.adoc | tr -d '| ' || true; }
receipt_recorded_legs() {
  [[ -f verification/legs/README.adoc ]] || return 3
  awk -F'|' 'function t(s){gsub(/^[[:space:]]+|[[:space:]]+$/,"",s); return s}
    /^\| [LA]-[0-9]+ \|/ { id=t($2); if (t($3)=="RECONCILED" && t($4)=="RECONCILED") ok[id]=1; else bad[id]=1 }
    END { for (i in ok) if (!(i in bad)) print i }' verification/legs/README.adoc
}

[[ "${BASH_SOURCE[0]}" == "$0" ]] || return 0
case "${1:-}" in
  --fetch-standards) fetch_standards; exit 0 ;;
  -h|--help|'') sed -n '5,25p' "$0" | sed 's/^# \{0,1\}//'; [[ -n "${1:-}" ]]; exit ;;
esac
check_standards
. "$RECEIPT_STD/scripts/proof-receipt.sh"
if [[ "${1:-}" == --sibling-cone ]]; then
  receipt_agda_cone src/Lintel/All.agda src "$SIBLING/src" | sed -n "s|^$SIBLING/||p" | LC_ALL=C sort
  exit 0
fi
receipt_main "$@"
