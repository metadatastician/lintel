#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# Run locally: bash tests/workflows/hypatia_scan_test.sh (requires yq v4 and jq).
set -euo pipefail

repo="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
static_workflow="$repo/.github/workflows/static-analysis-gate.yml"
dogfood_workflow="$repo/.github/workflows/dogfood-gate.yml"
fixture=$(mktemp -d)
trap 'rm -rf "$fixture"' EXIT

fail() {
    printf 'FAIL: %s\n' "$*" >&2
    exit 1
}

assert_equal() {
    local expected="$1" actual="$2" label="$3"
    [[ "$actual" == "$expected" ]] || fail "$label: expected [$expected], got [$actual]"
}

assert_contains() {
    local file="$1" snippet="$2"
    grep -Fq -- "$snippet" "$file" || fail "$file: missing [$snippet]"
}

# The scanner cache must not restore a build from before the fix or from
# another OTP patch release. Both consumers must use the fixed toolchain.
expected_ref=6693f9aed8e4383f78a3d01b600b32663bf7a45c
expected_otp=27.3.4.19
static_otp=$(yq -r '.jobs."hypatia-scan".steps[] | select(.uses | test("^erlef/setup-beam@")) | .with."otp-version"' "$static_workflow")
dogfood_otp=$(yq -r '.jobs."rsr-score-self".steps[] | select(.uses | test("^erlef/setup-beam@")) | .with."otp-version"' "$dogfood_workflow")
dogfood_ref=$(yq -r '.jobs."rsr-score-self".steps[] | select(.with.repository == "hyperpolymath/hypatia") | .with.ref' "$dogfood_workflow")
static_ref=$(yq -r '.jobs."hypatia-scan".steps[] | select(.id == "build") | .run' "$static_workflow" |
    sed -nE 's/^[[:space:]]*git .* fetch .* origin ([[:xdigit:]]+)[[:space:]]*$/\1/p')
cache_key=$(yq -r '.jobs."hypatia-scan".steps[] | select(.id == "cache-hypatia") | .with.key' "$static_workflow")
assert_equal "$expected_ref" "$static_ref" 'scanner Hypatia revision'
assert_equal "$expected_ref" "$dogfood_ref" 'dogfood Hypatia revision'
assert_equal "$expected_otp" "$static_otp" 'scanner OTP release'
assert_equal "$expected_otp" "$dogfood_otp" 'dogfood OTP release'
[[ "$cache_key" == *"-otp${expected_otp}-"* && "$cache_key" == *"-${expected_ref}" ]] ||
    fail "scanner cache key must include the full OTP release and Hypatia revision: $cache_key"

scan=$(yq -r '.jobs."hypatia-scan".steps[] | select(.id == "scan") | .run' "$static_workflow")
[[ -n "$scan" && "$scan" != null ]] || fail 'scan step is missing its run block'

mkdir -p "$fixture/home/hypatia" "$fixture/bin"
cat > "$fixture/home/hypatia/hypatia-cli.sh" <<'STUB'
#!/usr/bin/env bash
if [[ "$SCANNER_EXIT" == 0 ]]; then
    printf '[]\n'
fi
exit "$SCANNER_EXIT"
STUB
cat > "$fixture/bin/erl" <<'STUB'
#!/usr/bin/env bash
touch runtime-probed
if [[ "$RUNTIME_AVAILABLE" == yes ]]; then
    printf '27 (erts 15.2.7.11)'
else
    printf 'erl unavailable\n' >&2
    exit 127
fi
STUB
chmod +x "$fixture/home/hypatia/hypatia-cli.sh" "$fixture/bin/erl"

# Check the real run block with a fresh workspace and runner output files.
run_scan() {
    local label="$1" scanner_exit="$2" runtime_available="$3" actual=0
    case_dir="$fixture/$label"
    mkdir "$case_dir"
    printf 'Existing summary\n' > "$case_dir/summary"
    : > "$case_dir/outputs"
    (
        cd "$case_dir"
        env -u BASH_ENV HOME="$fixture/home" PATH="$fixture/bin:$PATH" \
            GITHUB_STEP_SUMMARY="$case_dir/summary" GITHUB_OUTPUT="$case_dir/outputs" \
            SCANNER_EXIT="$scanner_exit" RUNTIME_AVAILABLE="$runtime_available" \
            bash --noprofile --norc -e -o pipefail -c "$scan"
    ) > "$case_dir/log" 2>&1 || actual=$?
    if [[ "$actual" != "$scanner_exit" ]]; then
        cat "$case_dir/log" >&2
        fail "$label: expected exit $scanner_exit, got $actual"
    fi
}

assert_no_crash_report() {
    assert_equal 'Existing summary' "$(cat "$case_dir/summary")" 'summary after non-crash'
    [[ ! -e "$case_dir/runtime-probed" ]] || fail "$case_dir: probed OTP without a crash"
}

assert_crash_report() {
    local status="$1" signal="$2" runtime="$3"
    assert_contains "$case_dir/log" "::error::Hypatia did not run: the Erlang VM was killed by $signal (exit $status) on OTP $runtime."
    assert_equal 1 "$(grep -c '^::error::' "$case_dir/log")" 'number of crash annotations'
    assert_equal 'Existing summary' "$(head -n 1 "$case_dir/summary")" 'summary prefix'
    assert_contains "$case_dir/summary" '## Hypatia scan: Erlang VM crash'
    assert_contains "$case_dir/summary" "- Signal: $signal (exit $status)"
    assert_contains "$case_dir/summary" "- Runtime: OTP $runtime"
    assert_contains "$case_dir/summary" 'No findings were produced.'
    [[ -e "$case_dir/runtime-probed" ]] || fail "$case_dir: crash did not probe OTP"
    [[ ! -s "$case_dir/outputs" ]] || fail "$case_dir: crash published findings counts"
}

run_scan success 0 yes
assert_no_crash_report
assert_equal '' "$(cat "$case_dir/log")" 'successful scan log'
assert_equal '[]' "$(cat "$case_dir/hypatia-findings.json")" 'successful findings'
assert_contains "$case_dir/outputs" 'total=0'

for status in 2 128; do
    run_scan "failure-$status" "$status" yes
    assert_no_crash_report
    assert_equal "::error::Hypatia scanner execution failed with exit $status" \
        "$(cat "$case_dir/log")" 'ordinary failure annotation'
    [[ ! -s "$case_dir/outputs" ]] || fail "$case_dir: failure published findings counts"
done

run_scan segfault 139 yes
assert_crash_report 139 SIGSEGV '27 (erts 15.2.7.11)'

run_scan runtime-unavailable 143 no
assert_crash_report 143 SIGTERM unknown

run_scan unrecognised-signal 255 yes
assert_crash_report 255 SIG127 '27 (erts 15.2.7.11)'

echo 'PASS: Hypatia workflow pins, cache key, and scan outcomes'
