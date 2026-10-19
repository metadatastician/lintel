#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
#
# repo-deed.sh — find, or rename, the one repo deed: <stem>_chora.deed.
#
# The deed's FILENAME carries the repo slug (deed dispatch: <stem>_chora.deed,
# deed.abnf v1.0.0), so `just repo-init` renames it at mint. The name it must
# rename FROM is the PARENT's slug, which differs per template — and repo-init
# is carried UNCHANGED into every repo it mints. Naming one template's file
# there made every second-generation mint rename nothing; the identity step
# then aborted on the missing <child>_chora.deed, while
# docs/architecture/REPOSITORY-MAP.adoc said the rename happened (measured on
# metadatastician/lintel, 2026-10-19).
#
# Finding the deed by SHAPE, not by an assumed name, is what makes the
# generator work from any template. A repo has exactly one repo deed: the
# manifest describes the repository, so its stem is the repository slug.
#
# Usage:
#   repo-deed.sh find   [DIR]        print the deed path; fail if not exactly one
#   repo-deed.sh rename DIR SLUG     rename it to <SLUG>_chora.deed; print the path
#
# Exit: 0 success; 1 no deed / more than one / bad slug / rename failed; 2 usage.
set -euo pipefail

usage() {
    echo "usage: repo-deed.sh find [DIR] | repo-deed.sh rename DIR SLUG" >&2
    exit 2
}

deed_path() {
    local dir="$1" found=()
    [ -d "$dir" ] || { echo "repo-deed: no such directory: $dir" >&2; exit 1; }
    shopt -s nullglob
    for candidate in "$dir"/*_chora.deed; do
        [ -f "$candidate" ] && found+=("$candidate")
    done
    shopt -u nullglob
    if (( ${#found[@]} == 0 )); then
        echo "repo-deed: no *_chora.deed at the root of $dir" >&2
        exit 1
    fi
    if (( ${#found[@]} > 1 )); then
        echo "repo-deed: more than one deed at the root of $dir: ${found[*]}" >&2
        echo "           the repo deed manifests one repository; keep exactly one" >&2
        exit 1
    fi
    printf '%s\n' "${found[0]}"
}

cmd="${1:-}"
case "$cmd" in
    find)
        dir="${2:-.}"
        deed_path "$dir"
        ;;
    rename)
        [ $# -eq 3 ] || usage
        dir="$2"; slug="$3"
        # The same shape repo-init enforces on the slug. A caller that skips
        # that prompt (or a future one) must not be able to write a filename
        # GitHub, a shell or a deed dispatcher cannot carry.
        [[ "$slug" =~ ^[A-Za-z0-9][A-Za-z0-9._-]*$ ]] \
            || { echo "repo-deed: invalid repo slug for a deed filename: $slug" >&2; exit 1; }
        current="$(deed_path "$dir")"
        wanted="$dir/${slug}_chora.deed"
        # Plain mv: the mint runs before the new repo's first commit, so there
        # is no history to preserve. Renames (not tokens) are how filenames
        # change — a token in a FILENAME is the brace-collapse hazard class
        # repo-init has already been burnt by.
        if [ "$current" != "$wanted" ]; then
            mv -- "$current" "$wanted"
        fi
        printf '%s\n' "$wanted"
        ;;
    *)
        usage
        ;;
esac
