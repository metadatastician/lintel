{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
module ProgramLinkLocal where
open import Lintel.Lattice
open import Lintel.Instance

-- Must typecheck: the link may be built where only the client reads it.
-- Same expression as tests/reject/ProgramLink.agda, written into the
-- client's local state instead of the address field; the witness is the
-- client-only flow of tests/accept/LinkToClient.agda.  So the refusal there
-- is of the destination, not of the composition.
valid : anyone ⊢ (local ≔ plus (var addr) (var qn))
valid = assign (flows ⊒-true ⊒-false ⊒-false)
