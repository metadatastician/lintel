#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# Offline configuration regressions for the caller migration in PR #28.
# Run with Bash and Mike Farah yq v4.
set -euo pipefail

repo="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
workflows="${1:-$repo/.github/workflows}"
lock="$workflows/actions.lock"
audit="$workflows/main-estate-audit.yml"

fail() { echo "FAIL: $*" >&2; exit 1; }
check() {
    local file="$1" expression="$2" message="$3"
    if ! yq -e "$expression" "$file" >/dev/null; then
        fail "${file##*/}: $message"
    fi
}

standards='metadatastician/standards'
composites='hyperpolymath/proven-cicd-and-workflows'
sha='[a-f0-9]{40}'
standards_pin=''
for name in governance rust-ci; do
    ref=$(yq -r ".jobs.\"$name\".uses" "$workflows/$name.yml")
    [[ $ref =~ ^$standards/\.github/workflows/$name-reusable\.yml@($sha)$ ]] ||
        fail "$name must call its reusable workflow at a full SHA under $standards (got $ref)"
    pin="${BASH_REMATCH[1]}"
    [[ -z $standards_pin || $standards_pin == "$pin" ]] ||
        fail 'governance and Rust CI must use the same standards revision'
    standards_pin="$pin"
done

# The expression contains literal GitHub Actions interpolation syntax.
# shellcheck disable=SC2016
check "$audit" '
    ((.on | length) == 3) and (.on | has("workflow_call"))
    and ((.on.push | length) == 1)
    and ((.on.push.branches | length) == 1) and (.on.push.branches[0] == "main")
    and ((.on.pull_request | length) == 1)
    and ((.on.pull_request.branches | length) == 1) and (.on.pull_request.branches[0] == "main")
    and ((.permissions | length) == 1) and (.permissions.contents == "read")
    and (.concurrency.group == "${{ github.workflow }}-${{ github.ref }}")
    and (.concurrency.cancel-in-progress == true)
' 'expected unfiltered main pushes/PRs, reusable entry point, read-only contents, and per-ref cancellation'
check "$audit" '
    .jobs | ((length == 1) and
        (.estate-audit | (has("runs-on") and ((has("uses") or has("if") or has("continue-on-error") or has("permissions")) | not))))
' 'expected one inline runner job with workflow permissions and no job-level gate bypass'

checkout=$(yq -r '.jobs.estate-audit.steps[0].uses' "$audit")
[[ $checkout =~ ^actions/checkout@$sha$ ]] || fail 'the audit must start with a SHA-pinned checkout'
check "$audit" '
    .jobs.estate-audit.steps[0] | (
        (.with | ((.["persist-credentials"] == false) and ((has("repository") or has("ref") or has("path")) | not)))
        and ((has("if") or has("continue-on-error")) | not)
    )
' 'checkout must fetch the triggering repository and revision into the workspace without retaining credentials'

# The original audit at cicd-suite@55556cf5ba71ba744695861503c13148d3915a5d
# defines this ordered roster. A duplicate must not hide a missing gate.
expected_gates=$(cat <<'GATES'
required-files-check
code-hygiene-check
manifest-check
idris2-abi-check
zig-hexadeca-check
contractile-validation-check
recipes-set-check
affirmation-check
referencing-check
semantic-audit-check
spdx-license-check
proof-runner-check
prat-check
custom-tools-check
www-compliance-check
boj-cartridge-check
formatting-check
badges-check
metrics-check
linguist-check
tests-benches-check
hosting-check
gitsea-check
trust-humans-check
secrets-check
vaulted-tokens-check
GATES
)

gates='.jobs.estate-audit.steps | to_entries | .[] | select(.key > 0) | .value'
gate_refs=$(yq -r "$gates | .uses" "$audit")
gate_names=()
audit_pin=''
while IFS= read -r ref; do
    [[ $ref =~ ^$composites/actions/([^/@]+)@($sha)$ ]] ||
        fail "expected a SHA-pinned composite from $composites (got $ref)"
    gate_names+=("${BASH_REMATCH[1]}")
    pin="${BASH_REMATCH[2]}"
    [[ -z $audit_pin || $audit_pin == "$pin" ]] || fail 'audit gates must share one revision'
    audit_pin="$pin"
done <<< "$gate_refs"
diff -u --label 'original audit gates' --label 'inline audit gates' \
    <(printf '%s\n' "$expected_gates") <(printf '%s\n' "${gate_names[@]}") ||
    fail 'the inline audit changed the original gate roster'
check "$audit" "[$gates | select(has(\"if\") or has(\"continue-on-error\"))] | length == 0" \
    'all audit gates must run by default and retain normal failure behavior'

standards_key="$standards@$standards_pin"
audit_key="$composites@$audit_pin"
for name in governance rust-ci; do
    check "$lock" ".workflows[\".github/workflows/$name.yml\"] | ((length == 1) and (.[0] == \"$standards_key\"))" \
        "$name must lock its reusable under its own workflow path"
done
check "$lock" ".workflows[\".github/workflows/main-estate-audit.yml\"] | sort | ((length == 2) and (.[0] == \"$checkout\") and (.[1] == \"$audit_key\"))" \
    'the audit must lock checkout and the composite repository instead of the retired reusable'
check "$lock" ".dependencies[\"$checkout\"].commit == \"sha1-${checkout#*@}\"" \
    'audit checkout must resolve to the selected commit'
check "$lock" ".dependencies[\"$standards_key\"] | ((.owner_id == 297579217) and (.repo_id == 1116521501) and (.commit == \"sha1-$standards_pin\"))" \
    'standards must resolve to the current owner, original repository, and selected commit'
check "$lock" ".dependencies[\"$audit_key\"] | ((.owner_id == 6759885) and (.repo_id == 1326697643) and (.commit == \"sha1-$audit_pin\"))" \
    'audit composites must resolve to the renamed repository and selected commit'
check "$lock" '.dependencies | [keys[] | select(test("^hyperpolymath/cicd-suite@"))] | length == 0' \
    'obsolete cicd-suite records must be removed'

# Closure alone passes if an edge and its destination are both removed.
# These are required nested repositories of the migrated callers/composites.
check_nested() {
    local parent="$1" child="$2" edge
    edge=$(yq -r ".dependencies[\"$parent\"].uses[] | select(test(\"^$child@$sha\$\"))" "$lock")
    [[ $edge =~ ^$child@($sha)$ ]] || fail "$parent must lock a pinned nested dependency on $child"
    check "$lock" ".dependencies[\"$edge\"].commit == \"sha1-${BASH_REMATCH[1]}\"" \
        "$edge must have a dependency record for the selected commit"
}
for child in actions/cache actions/checkout denoland/setup-deno dtolnay/rust-toolchain \
    editorconfig-checker/action-editorconfig-checker erlef/setup-beam goto-bus-stop/setup-zig \
    oven-sh/setup-bun swatinem/rust-cache; do
    check_nested "$standards_key" "$child"
done
for child in hyperpolymath/deed-ecosystem hyperpolymath/k9-ecosystem; do
    check_nested "$audit_key" "$child"
done

check "$workflows/estate-rules.yml" '
    .jobs."estate-rules" |
    (((has("if") or has("continue-on-error")) | not)
    and ([.steps[] | select(.run == "bash tests/workflows/reusable_callers_startup_test.sh")
        | select((has("if") or has("continue-on-error")) | not)] | length == 1))
' 'Estate Rules must run the caller regression and propagate its failures'

# Exercise the guard itself with one change at a time. A fixture invocation
# runs only the assertions above so it cannot recursively run these controls.
if [[ $# -eq 0 ]]; then
    fixture=$(mktemp -d)
    trap 'rm -rf -- "$fixture"' EXIT
    cp -- "$lock" "$audit" "$workflows/"{governance,rust-ci,estate-rules}.yml "$fixture/"

    expect_rejection() {
        local file="$1" edit="$2" diagnostic="$3" output status=0
        yq -i "$edit" "$fixture/$file"
        output=$(bash "${BASH_SOURCE[0]}" "$fixture" 2>&1) || status=$?
        [[ $status == 1 && $output == *"FAIL: "*"$diagnostic"* ]] ||
            fail "expected $file fixture to fail with '$diagnostic' (exit $status): $output"
        cp -- "$workflows/$file" "$fixture/$file"
    }

    expect_rejection governance.yml '.jobs.governance.uses |= sub("@.*$", "@main")' \
        'governance must call its reusable workflow at a full SHA'
    expect_rejection main-estate-audit.yml '.on.pull_request.paths = ["docs/**"]' \
        'expected unfiltered main pushes/PRs'
    expect_rejection main-estate-audit.yml '.jobs.estate-audit.steps[1].continue-on-error = true' \
        'all audit gates must run by default and retain normal failure behavior'
    expect_rejection actions.lock 'del(.dependencies[] | select(.repo_id == 1326697643).uses[])' \
        'must lock a pinned nested dependency on hyperpolymath/deed-ecosystem'
    expect_rejection estate-rules.yml '
        (.jobs."estate-rules".steps[] | select(.run == "bash tests/workflows/reusable_callers_startup_test.sh")).if = false
    ' 'Estate Rules must run the caller regression and propagate its failures'
fi

echo 'PASS: migrated reusable callers, inline estate audit, and startup lock records'
