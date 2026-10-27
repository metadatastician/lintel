{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
module ProgramFieldGuarded where
open import Lintel.Lattice
open import Lintel.Instance

-- Must typecheck: the positive control for
-- tests/reject/ProgramLinkImplicit.agda.  A guard on the address may decide
-- a write to the address.  Same shape and witness.
valid : anyone ⊢ ifz (var addr) (addr ≔ var addr) skip
valid = ifz (assign (flows ⊒-true ⊒-true ⊒-false)) skip
