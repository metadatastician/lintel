#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
#
# The canonical Agda flag set for this repository: ONE definition, read by
# scripts/check.sh (the gate) and scripts/grade-receipt.sh (the receipt), so
# the receipt cannot describe a gate that did not run.  Pattern:
# hyperpolymath/secret-types scripts/proof-flags.sh.
#
# Conformance: standards/3-practice/PROOF-POLICY.adoc §2.1 (2026-11-01) sets
#   agda --safe --without-K --cubical-compatible <module.agda>
# as the estate default for first-party Agda theory entrypoints, and §8.2
# grants PWG-3 only under it.  Every flag below is that default or stronger:
#
#   --safe                policy default: no postulates, no --type-in-type,
#                         no termination pragmas, no unsafe features
#   --without-K           policy default (implied by --cubical-compatible;
#                         kept explicit so the intent survives a flag change)
#   --cubical-compatible  policy default.  No clause relies on constructor
#                         injectivity; -W error makes any
#                         -WUnsupportedIndexedMatch fatal, so a regression fails
#                         the gate instead of weakening it
#   --no-libraries        stronger: builtins only; the sibling comes in as an
#                         explicit -i path at its pin (scripts/fetch-siblings.sh)
#   --ignore-interfaces   stronger: no stale .agdai stands in for a proof
#   --double-check        stronger: the kernel re-verifies every term
#   -W error              stronger: a warning is a failure
#
# Dropping or weakening a flag needs a recorded owner decision and a new receipt.

# Print the canonical Agda arguments, one per line (-W and error separately).
proof_flags() {
  printf '%s\n' \
    --safe \
    --without-K \
    --cubical-compatible \
    --no-libraries \
    --ignore-interfaces \
    --double-check \
    -W error
}

# The flags as one line, for prose records and the receipt.
proof_flags_line() {
  proof_flags | paste -sd ' ' -
}

# The exact Agda version this repository pins (Debian 13's agda-bin); keep in
# step with .github/workflows/proofs.yml.
proof_agda_pin() {
  printf '%s\n' '2.6.4.3'
}

# Human-readable summary of what the pin is.
proof_agda_provenance() {
  printf '%s\n' 'Debian 13 agda-bin=2.6.4.3-1+b2'
}
