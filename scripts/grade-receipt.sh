#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
#
# grade-receipt.sh [--write|--check] [--commit <sha>]
#
# Writes (or checks) verification/receipts/agda-pwg_praxis.deed: the machine
# record of Lintel's Agda claims and their Proof Witness Grades
# (standards/3-practice/PROOF-POLICY.adoc §8, owner ruling 2026-11-04).
# Pattern: hyperpolymath/secret-types scripts/grade-receipt.sh.
#
#   PWG-2ii (§8.2): the Agda proof is PROVEN under the canonical §2.1
#   invocation, and both the Rocq and the Lean leg count: kernel-checked
#   (scripts/check-legs.sh, no axioms) and RECONCILED against the Agda
#   statement (verification/legs/README.adoc).  Not PWG-1: that needs a
#   per-commit receipt of each checker's observed result, which this file is not.
#
# The receipt is DERIVED from the tree, except for the claim list below, which
# is cross-checked in both directions against the claim IDs of README.adoc's
# claim table.  It records the import cone (§8.2): every Lintel module and
# every secret-types module they reach, with the sibling's pinned commit and a
# sha256 per file.  It does not run Agda: the gate (scripts/check.sh, in
# .github/workflows/proofs.yml) is the execution evidence, and the receipt says
# which gate produced which result (PROOF-POLICY §2.3).
#
# Run scripts/fetch-siblings.sh first: the cone is hashed from the sibling
# checkout at its pin.
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.."
. scripts/proof-flags.sh

out=verification/receipts/agda-pwg_praxis.deed
deps="${DEPENDENCIES_DIR:-_build/dependencies}"
st="${SECRET_TYPES_SRC:-$deps/secret-types/src}"
mode=
commit_override=
while (( $# )); do
  case "$1" in
    --write|--check) mode="$1" ;;
    --commit)        commit_override="${2:-}"; shift ;;
    -h|--help)
      printf 'usage: %s [--write|--check] [--commit <sha>]\n' "${0##*/}"
      exit 0 ;;
    *) printf 'unknown argument: %s\n' "$1" >&2; exit 2 ;;
  esac
  shift
done

# ── The claim list ────────────────────────────────────────────────────────────
# id | ledger token (README-EXPLAINME-STANDARD §5: proven | proven-with-postulates
# | tested-only | argued | open) | PWG (PROOF-POLICY §8.5: 3 | 2i | 2ii | 1 |
# ungraded; n/a for what is not a theory theorem, §8.1) | Rocq leg | Lean leg
# (§2: transported | re-proved | waived | unavailable).
claims() {
  cat <<'ROWS'
L-1|proven|2ii|re-proved|re-proved
L-2|proven|2ii|re-proved|re-proved
L-3|proven|2ii|re-proved|re-proved
L-4|proven|2ii|re-proved|re-proved
L-5|tested-only|n/a|n/a|n/a
L-6|proven|2ii|re-proved|re-proved
L-7|proven|2ii|re-proved|re-proved
A-1|argued|n/a|n/a|n/a
ROWS
}

# ── Derived facts ─────────────────────────────────────────────────────────────
repo="metadatastician/lintel"
source_commit="${commit_override:-$(git rev-parse --short=12 HEAD 2>/dev/null || printf 'unknown')}"
sibling_pin="$(sed -nE 's/^SECRET_TYPES_COMMIT="\$\{SECRET_TYPES_COMMIT:-([0-9a-f]{40})\}"$/\1/p' scripts/fetch-siblings.sh)"
[[ "$sibling_pin" =~ ^[0-9a-f]{40}$ ]] || { echo 'ERROR: no 40-hex secret-types pin in scripts/fetch-siblings.sh' >&2; exit 1; }
if [ ! -d "$st" ]; then
  echo "ERROR: secret-types sources not found at $st (run scripts/fetch-siblings.sh)" >&2
  exit 1
fi

# Print Lintel's module paths in sorted order.
own_modules() { find src/Lintel -name '*.agda' | LC_ALL=C sort; }
# Print the fixtures (positive controls and expected rejections) in sorted order.
fixtures() { find tests/accept tests/reject -name '*.agda' | LC_ALL=C sort; }

# Print the SecretTypes module names a file imports.
st_imports() {
  sed -nE 's/^[[:space:]]*(open[[:space:]]+)?import[[:space:]]+(SecretTypes(\.[A-Za-z0-9_′]+)*).*/\2/p' "$1"
}

# Print the sibling's import cone: every SecretTypes module reached from
# Lintel's modules, transitively, as paths relative to the sibling's src.
sibling_cone() {
  local -A seen=()
  local -a queue=()
  local f m p
  while read -r f; do
    while read -r m; do [ -n "$m" ] && queue+=("$m"); done < <(st_imports "$f")
  done < <(own_modules)
  while (( ${#queue[@]} )); do
    m="${queue[0]}"; queue=("${queue[@]:1}")
    [ -n "${seen[$m]:-}" ] && continue
    seen[$m]=1
    p="${m//.//}.agda"
    if [ ! -f "$st/$p" ]; then
      echo "ERROR: $m is imported but $st/$p does not exist" >&2
      return 1
    fi
    while read -r f; do [ -n "$f" ] && queue+=("$f"); done < <(st_imports "$st/$p")
  done
  printf '%s\n' "${!seen[@]}" | sed 's|\.|/|g; s|$|.agda|' | LC_ALL=C sort
}

# Print escape-hatch lines from Lintel's Agda files (the sibling has its own
# receipt and gate for its tree).
escape_hits() {
  grep -rn --include='*.agda' -E \
    '(^|[^A-Za-z])(postulate|believe_me|trustMe|sorry|Admitted)([^A-Za-z]|$)|{-# *(TERMINATING|NON_TERMINATING) *#-}|--type-in-type' \
    src/Lintel tests/accept tests/reject 2>/dev/null || true
}

# The claim list and README.adoc's claim table must name exactly the same
# claims; one without the other is drift, in either direction.
check_claim_ids() {
  local decl doc
  decl="$(claims | cut -d'|' -f1 | LC_ALL=C sort)"
  doc="$(grep -oE '^\| [LA]-[0-9]+$' README.adoc | tr -d '| ' | LC_ALL=C sort -u || true)"
  if [[ -z "$doc" ]]; then
    echo 'ERROR: no claim ids found in README.adoc; the table layout changed' >&2
    exit 1
  fi
  if [[ "$decl" != "$doc" ]]; then
    echo 'ERROR: claim ids differ between this receipt and README.adoc' >&2
    diff <(printf '%s\n' "$doc") <(printf '%s\n' "$decl") \
      | sed 's/^</  only in README.adoc:/; s/^>/  only in grade-receipt.sh:/' >&2
    exit 1
  fi
}

# Print repository-relative Rocq sources, then Lean sources (excluding .lake),
# each group sorted, followed by the Lean package and toolchain files.
leg_sources() {
  find verification/legs/rocq -name '*.v' | LC_ALL=C sort
  find verification/legs/lean -name '*.lean' -not -path '*/.lake/*' | LC_ALL=C sort
  printf '%s\n' verification/legs/lean/lakefile.toml verification/legs/lean/lean-toolchain
}
# Print the fixed list of leg inputs relative to the secret-types checkout.
sibling_leg_sources() {
  printf '%s\n' verification/legs/rocq/SecretTypes.v verification/legs/lean/SecretTypes/Generic.lean \
    verification/legs/lean/lakefile.toml verification/legs/lean/lean-toolchain
}

# Print the (legs) block: per leg, the pinned checker, its invocation, the
# axiom check, and the sha256 of every input, the sibling's leg files
# included.  The pins are read from scripts/check-legs.sh, which the gate uses.
# Write to stdout without running either checker. A missing sibling leg input
# reports an error to stderr and returns 1; stdout may already contain output.
emit_legs() {
  local coq lean sib="$deps/secret-types"
  coq="$(sed -n 's/^COQ_VERSION=\(.*\)$/\1/p' scripts/check-legs.sh)"
  lean="$(sed -n 's/^LEAN_VERSION=\(.*\)$/\1/p' scripts/check-legs.sh)"
  printf '  (legs\n    :gate "bash scripts/check-legs.sh"\n    :ci ".github/workflows/proofs.yml (job legs)"\n'
  printf '    :correspondence "verification/legs/README.adoc"\n'
  printf '    :route "re-proved"\n'
  printf '    :route-reason "Agda2Dedukti is an Agda backend pinned to a fork (b026db1, GHC 8.10) and cannot run on Agda %s; no released Dedukti/Lambdapi exporter to Lean 4, and no pinned route to Rocq"\n' "$(proof_agda_pin)"
  printf '    :state "RECONCILED"\n'
  printf '    :review "statement comparison written by Claude Code; provisional until owner review (estate doctrine 4)"\n'
  printf '    :depends-on "secret-types legs at the sibling pin (record, language, typing, TINI): imported, not restated"\n'
  printf '    (leg :prover "rocq" :checker "coqc" :version "%s" :invocation "coqc -q -Q <sibling>/verification/legs/rocq SecretTypesLeg Lintel.v (in verification/legs/rocq)" :libraries "secret-types Rocq leg only (no standard library)" :axioms "none (Print Assumptions: Closed under the global context)")\n' "$coq"
  printf '    (leg :prover "lean" :checker "lean" :version "%s" :invocation "lake build; lake env lean Axioms.lean (in verification/legs/lean)" :libraries "secret-types Lean leg only (no Mathlib)" :axioms "none (#print axioms: does not depend on any axioms)")\n' "$lean"
  printf '    (inputs\n'
  while read -r p; do
    printf '      (input :path "%s" :sha256 "%s")\n' "$p" "$(sha256sum "$p" | cut -d' ' -f1)"
  done < <(leg_sources)
  while read -r p; do
    [ -f "$sib/$p" ] || { echo "ERROR: sibling leg file $sib/$p missing (run scripts/fetch-siblings.sh)" >&2; return 1; }
    printf '      (input :repository "hyperpolymath/secret-types" :path "%s" :sha256 "%s")\n' "$p" "$(sha256sum "$sib/$p" | cut -d' ' -f1)"
  done < <(sibling_leg_sources)
  printf '    ))\n'
}

# A leg counted for a claim must have a row in the correspondence record, and
# the reverse: the grade is derived from the §2.2 record (PROOF-POLICY §8.4).
# On a mismatch, report the differing claim IDs to stderr and exit the script
# with status 1; matching records produce no output.
check_leg_records() {
  local rec=verification/legs/README.adoc counted recorded
  counted="$(claims | awk -F'|' '$4=="re-proved"||$5=="re-proved"{print $1}' | LC_ALL=C sort)"
  recorded="$(grep -oE '^\| [LA]-[0-9]+$' "$rec" 2>/dev/null | tr -d '| ' | LC_ALL=C sort -u || true)"
  if [[ "$counted" != "$recorded" ]]; then
    echo "ERROR: claims with a counted leg differ from the rows of $rec" >&2
    diff <(printf '%s\n' "$recorded") <(printf '%s\n' "$counted") \
      | grep -E '^[<>]' | sed "s|^<|  only in $rec:|; s/^>/  only in grade-receipt.sh:/" >&2
    exit 1
  fi
}

# Print the derived receipt.
emit() {
  local cone
  cone="$(sibling_cone)"
  printf ';; SPDX-License-Identifier: CC-BY-SA-4.0\n'
  printf ';; SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell\n'
  printf ';; GENERATED by scripts/grade-receipt.sh; regenerate with --write, check with --check.\n'
  printf ';; This describes the gate and tree; the CI log is the execution evidence.\n'
  printf '(praxis-deed\n  :schema-version "1.0.0"\n  :canonical-name "lintel-agda-pwg-receipt"\n'
  printf '  (identity\n    :project "lintel"\n    :name "agda verification receipt (Proof Witness Grades)"\n'
  printf '    :repository "%s"\n    :repo-uuid #u5"github.com/%s"\n' "$repo" "$repo"
  printf '    :kind "theory"\n    :source-commit "%s")\n' "$source_commit"
  printf '  (prover\n    :tool "agda"\n    :version "%s"\n    :provenance "%s"\n' "$(proof_agda_pin)" "$(proof_agda_provenance)"
  printf '    :library "none (--no-libraries; Agda builtins and the pinned sibling only)"\n    :flags "%s"\n' "$(proof_flags_line)"
  printf '    :flags-source "scripts/proof-flags.sh")\n'
  printf '  (conformance\n    :policy "standards/3-practice/PROOF-POLICY.adoc"\n'
  printf '    :policy-revision "section 2.1 dated 2026-11-01; section 8 (PWG) dated 2026-11-04"\n'
  printf '    :canonical-invocation "agda --safe --without-K --cubical-compatible"\n'
  printf '    :cubical-compatible "met"\n'
  printf '    :stronger-than-canonical ("--no-libraries" "--ignore-interfaces" "--double-check" "-W error"))\n'
  printf '  (gate\n    :command "bash scripts/check.sh"\n    :ci ".github/workflows/proofs.yml"\n'
  printf '    :module-count %s\n    :fixture-count %s)\n' "$(own_modules | wc -l | tr -d ' ')" "$(fixtures | wc -l | tr -d ' ')"
  printf '  (trust-base\n    :postulates %s\n    :escape-hatches %s\n' \
    "$(grep -rlw --include='*.agda' postulate src/Lintel tests/accept tests/reject 2>/dev/null | wc -l | tr -d ' ')" \
    "$(escape_hits | wc -l | tr -d ' ')"
  printf '    :library-dependencies 0\n    :axioms-assumed 0\n'
  printf '    :assumption "A-1 non-collusion is a stated hypothesis of the threat model (argued), not an axiom of any proof")\n'
  printf '  ; PWGs apply to theory theorems (PROOF-POLICY section 8.1); L-5 (refusal fixtures) and A-1 (an assumption) are n/a.\n'
  printf '  ; Rocq and Lean legs: re-proved by hand on top of secret-types'"'"' legs, RECONCILED in verification/legs/README.adoc.\n'
  emit_legs
  printf '  (claims\n'
  while IFS='|' read -r id token pwg coq lean; do
    printf '    (claim :id "%s" :token "%s" :pwg "%s" :coq-leg "%s" :lean-leg "%s")\n' "$id" "$token" "$pwg" "$coq" "$lean"
  done < <(claims)
  printf '  )\n  ; The import cone: every module the proofs rest on, hashed.\n  (modules\n'
  while read -r m; do
    printf '    (module :path "%s" :sha256 "%s")\n' "$m" "$(sha256sum "$m" | cut -d' ' -f1)"
  done < <(own_modules)
  printf '  )\n  (sibling\n    :repository "hyperpolymath/secret-types"\n    :commit "%s"\n' "$sibling_pin"
  while read -r m; do
    printf '    (module :path "src/%s" :sha256 "%s")\n' "$m" "$(sha256sum "$st/$m" | cut -d' ' -f1)"
  done <<< "$cone"
  printf '  )\n  (fixtures\n'
  while read -r f; do
    printf '    (fixture :path "%s")\n' "$f"
  done < <(fixtures)
  printf '  )\n)\n'
}

check_claim_ids
check_leg_records

case "$mode" in
  --write|"")
    mkdir -p "$(dirname "$out")"
    emit > "$out"
    printf 'WROTE %s (source-commit %s)\n' "$out" "$source_commit"
    ;;
  --check)
    tmp="$(mktemp)"; diff_out="$(mktemp)"; trap 'rm -f "$tmp" "$diff_out"' EXIT
    emit > "$tmp"
    # The source-commit line is expected to differ: a committed receipt names
    # its parent.  Everything else must match byte for byte.
    filter() { grep -v '^    :source-commit ' "$1"; }
    if ! diff -u <(filter "$out") <(filter "$tmp") > "$diff_out" 2>&1; then
      echo 'ERROR: verification receipt does not match the tree:' >&2
      sed -n '1,60p' "$diff_out" >&2
      echo 'Regenerate with: bash scripts/grade-receipt.sh --write' >&2
      exit 1
    fi
    echo "PASS: verification receipt matches the tree ($(own_modules | wc -l | tr -d ' ') Lintel modules, $(sibling_cone | wc -l | tr -d ' ') sibling modules, all sha256 verified)"
    ;;
esac
