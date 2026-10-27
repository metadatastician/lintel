{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
module ProgramLinkImplicit where
open import Lintel.Lattice
open import Lintel.Instance

-- Must fail: the same link built implicitly.  The address field is rewritten
-- under a guard on the query name, so whether it changes reveals the query
-- name to the proxy.  The program counter is qname, the write's label
-- qname ⊔ address, and the proxy bit fails as in ProgramLink.  The positive
-- control is tests/accept/ProgramFieldGuarded.agda: guarded on the address
-- itself, under the same witness.
invalid : anyone ⊢ ifz (var qn) (addr ≔ var addr) skip
invalid = ifz (assign (flows ⊒-true ⊒-true ⊒-false)) skip
