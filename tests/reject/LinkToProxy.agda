{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
module LinkToProxy where
open import Lintel.Lattice

-- Must fail: a self-defeating composition.  It shows the proxy the client's
-- address and the query name together.  address ⊔ qname is the client's
-- alone, so at the proxy bit the flow needs a closed reader set to admit the
-- proxy (false ⊒ true): the top-flows-to-bottom case, one role at a time.
-- The client and target witnesses are the CORRECT ones (true ⊒ false and
-- false ⊒ false), so the proxy bit is the only failing witness: a regression
-- that permitted the proxy flow would make this module typecheck, and the
-- rejection gate would report it.
invalid : address ⊔ qname ⊑ observer proxy
invalid = flows ⊒-true ⊒-true ⊒-false
