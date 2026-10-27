{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
module ProgramLink where
open import Lintel.Lattice
open import Lintel.Instance

-- Must fail: a program that builds the link.  It adds the query name to the
-- address and stores the sum in the address field, which the proxy reads.
-- The value is labelled address ⊔ qname, the client's alone, so at the proxy
-- bit the assignment needs false ⊒ true.  The client and target witnesses
-- are the correct ones, and tests/accept/ProgramField.agda types the same
-- assignment with `lit 0` in place of `var qn` under the same witness, so
-- the query name is the only difference.  tests/accept/ProgramLinkLocal.agda
-- writes the same sum into the client's local state, which is allowed.
invalid : anyone ⊢ (addr ≔ plus (var addr) (var qn))
invalid = assign (flows ⊒-true ⊒-true ⊒-false)
