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
#   PWG-3 (§8.2): the Agda proof is PROVEN under the canonical §2.1 invocation
#   and no Rocq or Lean recheck leg counts yet.  PWG-3 is not a discharge
#   (§8.4): every PWG-3 theorem still owes both legs.
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
L-1|proven|3|unavailable|unavailable
L-2|proven|3|unavailable|unavailable
L-3|proven|3|unavailable|unavailable
L-4|proven|3|unavailable|unavailable
L-5|tested-only|n/a|n/a|n/a
L-6|proven|3|unavailable|unavailable
L-7|proven|3|unavailable|unavailable
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
  printf '  ; Independent Rocq and Lean legs remain unavailable: no transport or hand re-proof.\n'
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
