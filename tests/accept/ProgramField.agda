{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
module ProgramField where
open import SecretTypes.Lang using (lo; var; lit; plus; _≔_)
open import Lintel.Lattice
open import Lintel.Instance

-- Must typecheck: the positive control for tests/reject/ProgramLink.agda.
-- Arithmetic on the address alone stays in the address field.  Same imports,
-- shape and witness, so a rejection there comes from the query name.
valid : anyone ⊢ (lo ≔ plus (var lo) (lit 0))
valid = assign (flows ⊒-true ⊒-true ⊒-false)
