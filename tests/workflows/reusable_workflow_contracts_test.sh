#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
#
# Offline configuration checks; requires Mike Farah yq v4 and jq.
# Usage: bash tests/workflows/reusable_workflow_contracts_test.sh [workflow-dir]
set -euo pipefail

repo=$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)
workflows=${1:-"$repo/.github/workflows"}

fail() { echo "FAIL: $*" >&2; exit 1; }

read_yaml() { yq -o=json '.' "$workflows/$1"; }
check() {
    local message=$1
    shift
    jq -e "$@" >/dev/null || fail "$message"
}

lock=$(read_yaml actions.lock)
for caller in governance rust-ci scorecard mirror; do
    workflow=$(read_yaml "$caller.yml")
    uses=$(jq -er --arg job "$caller" '.jobs[$job].uses' <<< "$workflow") ||
        fail "$caller must call a reusable workflow at job level"
    expected="metadatastician/standards/.github/workflows/$caller-reusable.yml"
    [[ ${uses%@*} == "$expected" && ${uses##*@} =~ ^[a-f0-9]{40}$ ]] ||
        fail "$caller must call $expected at a full commit SHA"

    # Check the full job path above, since the lock sync gate only sees owner/repo@ref.
    ref="metadatastician/standards@${uses##*@}"
    check "$caller must lock its standards call to the same commit" \
        --arg file ".github/workflows/$caller.yml" --arg ref "$ref" --arg sha "${uses##*@}" '
        .workflows[$file] == [$ref] and .dependencies[$ref].commit == ("sha1-" + $sha)
    ' <<< "$lock"

    if [[ $caller != scorecard ]]; then
        check "$caller must grant read access to actions and contents" --arg job "$caller" '
            (.jobs[$job].permissions // .permissions) == {"actions":"read","contents":"read"}
        ' <<< "$workflow"
    fi
    case "$caller" in
        scorecard)
            # Job permissions replace the workflow permissions; these grants are needed
            # for the Packaging check, SARIF upload, and OIDC publication.
            check "Scorecard needs the complete permissions block on the calling job" '
                .jobs.scorecard.permissions ==
                {"actions":"read","contents":"read","security-events":"write","id-token":"write"}
            ' <<< "$workflow"
            ;;
        mirror)
            check "Mirror must keep its seven explicit mappings without inheriting secrets" '
                .jobs.mirror.secrets ==
                (["GITLAB_SSH_KEY","BITBUCKET_SSH_KEY","CODEBERG_SSH_KEY","SOURCEHUT_SSH_KEY",
                  "DISROOT_SSH_KEY","GITEA_SSH_KEY","RADICLE_KEY"]
                 | map({key: ., value: ("${{ secrets." + . + " }}")}) | from_entries)
            ' <<< "$workflow"
            ;;
    esac

    # A lock can be internally closed while silently omitting an actual nested use.
    case "$caller" in
        rust-ci) nested='["dtolnay/rust-toolchain", "swatinem/rust-cache"]' ;;
        scorecard) nested='["ossf/scorecard-action"]' ;;
        mirror) nested='["webfactory/ssh-agent"]' ;;
        *) continue ;;
    esac
    check "$caller must lock its nested actions: $nested" --arg ref "$ref" --argjson nested "$nested" '
        .dependencies as $deps |
        all($nested[];
            . as $action |
            any($deps[$ref].uses[]?;
                . as $pin |
                split("@") as [$repo, $sha] |
                $repo == $action and ($sha | test("^[a-f0-9]{40}$")) and
                $deps[$pin].commit == ("sha1-" + $sha)))
    ' <<< "$lock"
done

audit=$(read_yaml main-estate-audit.yml)
check "Audit must run on main pushes and PRs and remain callable, with read-only contents" '
    .on == {"push":{"branches":["main"]},"pull_request":{"branches":["main"]},"workflow_call":null} and
    .permissions == {"contents":"read"} and
    ((.jobs["estate-audit"].permissions // {"contents":"read"}) == {"contents":"read"})
' <<< "$audit"

check "Audit must cancel superseded runs within the same workflow and ref" '
    .concurrency == {"group":"${{ github.workflow }}-${{ github.ref }}","cancel-in-progress":true}
' <<< "$audit"

check "Audit must run inline and check out the caller before the gates, without retaining credentials" '
    .jobs["estate-audit"] |
    has("runs-on") and (has("uses") | not) and (has("if") | not) and
    ((.["continue-on-error"] // false) == false) and
    (.steps[0] |
        (.uses | test("^actions/checkout@[a-f0-9]{40}$")) and
        (has("if") | not) and .with == {"persist-credentials":false})
' <<< "$audit"

# Gate IDs from the former reusable audit at 55556cf, independent of the inline YAML.
# Sort the IDs: checkout must be first, but the gates need not follow a fixed order.
check "Audit must run every upstream gate once, unconditionally, at a full SHA" '
    .jobs["estate-audit"].steps[1:] as $gates |
    all($gates[];
        (.uses | test("^hyperpolymath/proven-cicd-and-workflows/actions/[^/@]+@[a-f0-9]{40}$")) and
        (has("if") | not) and ((.["continue-on-error"] // false) == false)) and
    ([$gates[].uses | split("/")[3] | split("@")[0]] | sort) ==
    (["required-files-check","code-hygiene-check","manifest-check","idris2-abi-check",
      "zig-hexadeca-check","contractile-validation-check","recipes-set-check","affirmation-check",
      "referencing-check","semantic-audit-check","spdx-license-check","proof-runner-check",
      "prat-check","custom-tools-check","www-compliance-check","boj-cartridge-check",
      "formatting-check","badges-check","metrics-check","linguist-check","tests-benches-check",
      "hosting-check","gitsea-check","trust-humans-check","secrets-check","vaulted-tokens-check"] | sort)
' <<< "$audit"

checkout=$(jq -er '.jobs["estate-audit"].steps[0].uses' <<< "$audit")
audit_ref="hyperpolymath/proven-cicd-and-workflows@$(jq -er '
    .jobs["estate-audit"].steps[1:] | map(.uses | split("@")[1]) | unique |
    if length == 1 then .[0] else error("audit gates must share one pin") end
' <<< "$audit")"
check "Audit must lock checkout and the composite bundle, including its pinned Deed and K9 dependencies" \
    --arg checkout "$checkout" --arg audit "$audit_ref" '
    . as $lock |
    (.workflows[".github/workflows/main-estate-audit.yml"] | sort) == ([$checkout, $audit] | sort) and
    all([$checkout, $audit][];
        . as $ref | $lock.dependencies[$ref].commit == ("sha1-" + ($ref | split("@")[1]))) and
    all(["deed-ecosystem", "k9-ecosystem"][];
        . as $repo |
        any($lock.dependencies[$audit].uses[]?;
            . as $ref |
            test("^hyperpolymath/" + $repo + "@[a-f0-9]{40}$") and
            $lock.dependencies[$ref].commit == ("sha1-" + ($ref | split("@")[1]))))
' <<< "$lock"

echo "PASS: reusable callers and inline estate audit satisfy their workflow and lock contracts"
