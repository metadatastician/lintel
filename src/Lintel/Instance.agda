{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
--
-- The reader-set lattice as an instance of secret-types' Lattice record, and
-- secret-types' generic TINI at it (README L-6).
--
--   reader-sets      the instance: Lintel.Lattice's ⊑, ⊔, anyone and the
--                    three laws the census needs (⊑-trans, ⊔-upper₁, ⊔-upper₂)
--   field-label      lo is the client's address, hi the query name
--   tini-per-role    TINI for each role's principal observer
--
-- Pin: hyperpolymath/secret-types ccdcb3ec42792337a9ab6047e1f99de9d20a4f96
--   SecretTypes.Lattice.Record, SecretTypes.Noninterference.Generic
--   (scripts/fetch-siblings.sh)
module Lintel.Instance where

open import SecretTypes.Prelude
open import SecretTypes.Lattice.Record
open import SecretTypes.Lang using (Var; lo; hi)
open import Lintel.Lattice

----------------------------------------------------------------------
-- The instance.  The record is secret-types'; only the fields are Lintel's.

reader-sets : Lattice
reader-sets = record
  { Carrier  = Label
  ; _⊑_      = _⊑_
  ; _⊔_      = _⊔_
  ; ⊥ₗ       = anyone
  ; ⊑-trans  = ⊑-trans
  ; ⊔-upper₁ = ⊔-upper₁
  ; ⊔-upper₂ = ⊔-upper₂
  }

-- The two variables of secret-types' fragment carry the two fields.
field-label : Var → Label
field-label lo = address
field-label hi = qname

open import SecretTypes.Noninterference.Generic reader-sets field-label public

----------------------------------------------------------------------
-- L-6: one principal observer per role.

-- The role's observer sees exactly what it may read (Lintel.Lattice,
-- observes-flow and flow-observes).
role : Role → Observer reader-sets
role r = principal reader-sets (observer r)

tini-per-role : ∀ r → TINI (Observer.sees (role r))
tini-per-role r = tini (role r)

