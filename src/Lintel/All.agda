{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
-- Every module of the development; scripts/check.sh checks this root and
-- fails if a module under src/Lintel is not imported here.
module Lintel.All where
import Lintel.Lattice
import Lintel.Instance
