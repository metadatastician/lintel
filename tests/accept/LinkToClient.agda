{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
module LinkToClient where
open import Lintel.Lattice

-- Must typecheck: the positive control.  The client may hold its own
-- address and query name together.  Same imports and shape as
-- tests/reject/LinkTo*.agda, so a rejection there comes from the label,
-- not from a broken import.
valid : address ⊔ qname ⊑ observer client
valid = flows ⊒-true ⊒-false ⊒-false
