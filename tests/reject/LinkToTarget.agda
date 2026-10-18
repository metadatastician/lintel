{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
module LinkToTarget where
open import Lintel.Lattice

-- Must fail: a self-defeating composition.  It shows the target the query
-- name and the client's address together, so at the target bit the flow
-- needs false ⊒ true.
invalid : address ⊔ qname ⊑ observer target
invalid = flows ⊒-true ⊒-false ⊒-true
