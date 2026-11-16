#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
#
# grade-receipt.sh: the gate of Lintel's proof receipt,
# verification/receipts/agda-pwg_praxis.deed (PROOF-POLICY §8.5).
#
#   --fetch-standards  fetch the pinned tools of the standard into
#                      _build/standards and check each one's sha256
#   --cross-check      the receipt's claims are README.adoc's theorems, and its
#                      counted legs are the RECONCILED rows of
#                      verification/legs/README.adoc (offline; no tools needed)
#   --check            --cross-check, then: the pinned reader accepts the
#                      receipt and derives its grades; the git checks of
#                      §8.5.3 hold (the shared checker, with the secret-types
#                      checkout as the clone of its import); every current
#                      receipt still describes HEAD; and the reader refuses the
#                      receipt with its first grade changed (negative control)
#   --write            regenerate the receipt from its source,
#                      verification/receipts/proof-receipt.toml, with the
#                      shared writer of the standard (scripts/proof-receipt.js)
#                      in the standards checkout at $STANDARDS_DIR
#
# The receipt is written, never typed: its source holds the claims, the run
# ledger (each row copied from the CI log of the run) and the trusted base, and
# the writer derives every manifest, digest, import and grade from git.  The
# gate needs only the reader, the reference digest script and the git checker,
# all at one pinned standards commit.  The writer is not pinned here yet: it is
# in standards#1626.  Once that merges, pin it with the others and let --check
# also regenerate the receipt (proof-receipt.js check).
#
# Run scripts/fetch-siblings.sh first: the receipt imports secret-types at its
# pin, and the git checks read that checkout.
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.."
export LC_ALL="${LC_ALL:-C.UTF-8}"

out=verification/receipts/agda-pwg_praxis.deed
src=verification/receipts/proof-receipt.toml
sibling="${DEPENDENCIES_DIR:-_build/dependencies}/secret-types"
default_branch=main
# Claims of README.adoc's table that are not theorems (§8.1), so they have no
# claim in the receipt: L-5 is a set of checked refusals, A-1 an assumption.
not_theorems=(L-5 A-1)

# The pinned standard: one commit, each file with its sha256.  At or after
# standards#1564, which added (import …) to the reader and the checker.
STANDARDS_COMMIT=f37ef5f62b7a18a769c8288f89a5a1a2a3db36f4
READER_SHA256=8978546740ca2d6a1d90b769fe02159883cb18f1eb2c44b2eeb737bab341dcd2
DIGEST_SHA256=dfc6dde01a3a79df638eebe4cad0eae584d8f17280077e149174c0667e9508f4
CHECKER_SHA256=f2375747238464535d1b4a61f658f07cb2f8504c69bfb1812311c79429a4e23e
STANDARDS_RAW="https://raw.githubusercontent.com/metadatastician/standards/$STANDARDS_COMMIT"
std=_build/standards
reader="$std/1-formats/deed/tools/deed_lint.js"
digest="$std/scripts/proof-inputs-sha256.sh"
checker="$std/scripts/check-proof-receipt.sh"

die() { printf 'ERROR: %s\n' "$*" >&2; exit 1; }
pinned() { # FILE SHA256 WHAT
  [[ -f "$1" ]] || die "the pinned $3 is missing at $1: run bash scripts/grade-receipt.sh --fetch-standards"
  [[ "$(sha256sum "$1" | cut -d' ' -f1)" == "$2" ]] || die "$1 is not the pinned $3 (sha256 differs)"
}
fetch() { # PATH SHA256 DEST
  mkdir -p "$(dirname "$3")"
  curl --proto '=https' --tlsv1.2 -fsSL "$STANDARDS_RAW/$1" -o "$3.tmp"
  echo "$2  $3.tmp" | sha256sum --check --strict >/dev/null || { rm -f "$3.tmp"; die "the fetched $1 does not match its pinned sha256"; }
  mv "$3.tmp" "$3"; printf 'FETCHED %s (standards %s)\n' "$1" "${STANDARDS_COMMIT:0:12}"
}

# ── Cross-checks against the human records (offline) ────────────────────────
# The receipt's layout is the writer's, and the reader checks its structure;
# these read only the claim heads and leg heads.
receipt_claims() { sed -nE 's/^  \(claim :id "([^"]+)".*/\1/p' "$out" | LC_ALL=C sort; }
# id|prover|state for each discharged rocq and lean leg of the receipt.
receipt_legs() {
  awk '
    /^  \(claim :id "/ { match($0, /"[^"]+"/); id = substr($0, RSTART + 1, RLENGTH - 2) }
    /^    \(leg :prover (rocq|lean) :route (re-proved|transported) / {
      p = $0; sub(/.*:prover /, "", p); sub(/ .*/, "", p)
      s = $0; sub(/.*:state /, "", s); sub(/[ )].*/, "", s)
      print id "|" p "|" s
    }' "$out" | LC_ALL=C sort
}
cross_check() {
  [[ -f "$out" ]] || die "$out is missing"
  local doc decl rec recorded counted
  doc="$(grep -oE '^\| [LA]-[0-9]+$' README.adoc | tr -d '| ' | LC_ALL=C sort -u || true)"
  [[ -n "$doc" ]] || die 'no claim ids found in README.adoc; the table layout changed'
  decl="$( { receipt_claims; printf '%s\n' "${not_theorems[@]}"; } | LC_ALL=C sort)"
  if [[ "$decl" != "$doc" ]]; then
    { diff <(printf '%s\n' "$doc") <(printf '%s\n' "$decl") || true; } \
      | grep -E '^[<>]' | sed "s/^</  only in README.adoc:/; s|^>|  only in the receipt (or not_theorems):|" >&2
    die 'claim ids differ between the receipt and README.adoc'
  fi
  rec=verification/legs/README.adoc
  recorded="$(awk -F'|' '
    function trim(s) { gsub(/^[[:space:]]+|[[:space:]]+$/, "", s); return s }
    /^\| [LA]-[0-9]+([[:space:]]|$)/ { print trim($2) "|rocq|" trim($3); print trim($2) "|lean|" trim($4) }
  ' "$rec" | LC_ALL=C sort)"
  counted="$(receipt_legs)"
  if [[ "$counted" != "$recorded" ]]; then
    { diff <(printf '%s\n' "$recorded") <(printf '%s\n' "$counted") || true; } \
      | grep -E '^[<>]' | sed "s|^<|  only in $rec:|; s/^>/  only in the receipt:/" >&2
    die "the receipt's legs and their states must be the rows of $rec"
  fi
  printf 'PASS: the receipt names README.adoc'"'"'s theorems (%s), and its legs are the rows of %s\n' \
    "$(receipt_claims | paste -sd ' ' -)" "$rec"
}

# ── The canon checks ────────────────────────────────────────────────────────
check() {
  cross_check
  command -v bun >/dev/null || die 'bun is needed to run the pinned reader'
  pinned "$reader" "$READER_SHA256" reader
  pinned "$digest" "$DIGEST_SHA256" 'reference digest script'
  pinned "$checker" "$CHECKER_SHA256" 'git checker'
  [[ -d "$sibling/.git" ]] || die "no secret-types checkout at $sibling: run bash scripts/fetch-siblings.sh"
  local json base
  json="$(bun "$reader" --proof-receipt-json "$out")" || die "the pinned reader refuses $out"
  printf 'PASS: the pinned reader (standards %s) accepts %s; source-commit %s\n' \
    "${STANDARDS_COMMIT:0:12}" "$out" "$(jq -r .source_commit <<<"$json")"
  jq -r '.claims[] | "  \(.id)  \(.pwg)  foundation-diverse \(.foundation_diverse)"' <<<"$json"

  base="refs/remotes/origin/$default_branch"
  git rev-parse -q --verify "$base" >/dev/null || base="refs/heads/$default_branch"
  bash "$checker" --branch "$base" --import "hyperpolymath/secret-types=$sibling" "$out" . \
    || die 'the git checks of PROOF-POLICY §8.5.3 failed'

  # Each current receipt must still describe HEAD: its manifest's digest at
  # HEAD is the digest it records.  A change to an input needs a new run.  A
  # new file in a cone comes with an import in a file the manifest lists, so a
  # cone that grows changes the digest too.  The writer's own check, once it
  # is pinned here, recomputes the whole input set instead.
  local head prover want paths got
  head="$(git rev-parse HEAD)"
  while IFS=$'\t' read -r prover want paths; do
    # shellcheck disable=SC2086
    got="$(bash "$digest" "$head" $paths)" || die "the $prover inputs of the receipt are not all files at HEAD"
    [[ "$got" == "$want" ]] || die "the $prover inputs changed since its run (recorded $want, HEAD gives $got): record a new run in $src and regenerate"
    if [[ -n "$(git status --porcelain -- $paths)" ]]; then die "the $prover inputs differ from HEAD in the working tree"; fi
    printf 'PASS: the %s receipt describes HEAD (%s)\n' "$prover" "${head:0:12}"
  done < <(jq -r '[.claims[].legs[] | . as $l | .receipts[] | select(.state == "current")
      | {prover: $l.prover, d: ."inputs-sha256", p: ([.inputs_manifest[].path] | join(" "))}] | unique[]
      | "\(.prover)\t\(.d)\t\(.p)"' <<<"$json")

  # Negative control: the same receipt with its first grade changed is refused.
  local first wrong err
  first="$(jq -r '.claims[0].pwg' <<<"$json")"
  case "$first" in PWG-1) wrong=PWG-2ii ;; *) wrong=PWG-1 ;; esac
  ctl="$(mktemp -d)"; trap 'rm -rf "${ctl:-}"' EXIT
  awk -v w="$wrong" '!done && /:pwg /{sub(/:pwg [A-Za-z0-9-]+/, ":pwg " w); done=1} {print}' "$out" > "$ctl/control_praxis.deed"
  if err="$(bun "$reader" --proof-receipt-json "$ctl/control_praxis.deed" 2>&1)"; then
    die "negative control: the reader accepted the first claim recorded as :pwg $wrong"
  fi
  grep -q 'records :pwg' <<<"$err" || { printf '%s\n' "$err" >&2; die 'negative control: refused for another reason than the grade'; }
  printf 'PASS: negative control (the first claim recorded as :pwg %s is refused: its legs support %s)\n' "$wrong" "$first"
}

case "${1:-}" in
  --fetch-standards)
    fetch 1-formats/deed/tools/deed_lint.js "$READER_SHA256" "$reader"
    fetch scripts/proof-inputs-sha256.sh "$DIGEST_SHA256" "$digest"
    fetch scripts/check-proof-receipt.sh "$CHECKER_SHA256" "$checker" ;;
  --cross-check) cross_check ;;
  --check) check ;;
  --write)
    writer="${STANDARDS_DIR:-}/scripts/proof-receipt.js"
    [[ -n "${STANDARDS_DIR:-}" && -f "$writer" ]] \
      || die 'set STANDARDS_DIR to a standards checkout that has scripts/proof-receipt.js (standards#1626)'
    bun "$writer" write "$src"
    cross_check ;;
  -h|--help|'') sed -n '5,33p' "$0" | sed 's/^# \{0,1\}//'; [[ -n "${1:-}" ]] ;;
  *) printf 'unknown argument: %s\n' "$1" >&2; exit 2 ;;
esac
