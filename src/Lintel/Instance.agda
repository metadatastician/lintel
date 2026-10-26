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
--   tini-coalition   TINI for any two roles observing together
--   collusion-gap    why A-1 stays: a coalition of proxy and target sees each
--                    field, though not their composition
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

----------------------------------------------------------------------
-- Coalitions.  A union of down-closed observers is down-closed, over any
-- Lattice; two roles observing together are the union of their observers.
-- In a reader-set lattice that union is not a principal observer.

infixr 1 _⊎_
data _⊎_ (A B : Set) : Set where
  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B

infixr 5 _∪_
_∪_ : ∀ {𝓛} → Observer 𝓛 → Observer 𝓛 → Observer 𝓛
V ∪ W = record
  { sees   = λ ℓ → Observer.sees V ℓ ⊎ Observer.sees W ℓ
  ; sees-↓ = λ { p (inj₁ v) → inj₁ (Observer.sees-↓ V p v)
               ; p (inj₂ w) → inj₂ (Observer.sees-↓ W p w) }
  }

coalition : Role → Role → Observer reader-sets
coalition r r' = role r ∪ role r'

tini-coalition : ∀ r r' → TINI (Observer.sees (coalition r r'))
tini-coalition r r' = tini (coalition r r')

-- TINI does not make collusion harmless.  Proxy and target together see
-- the address and the query name, each by a permitted flow, and can join
-- them outside any program; what they do not see is the composite label.
-- So L-4's confinement of the link is still per role (README A-1).
collusion-gap : Observer.sees (coalition proxy target) address
              × Observer.sees (coalition proxy target) qname
              × ¬ Observer.sees (coalition proxy target) (address ⊔ qname)
collusion-gap = inj₁ address-to-proxy , inj₂ qname-to-target , λ
  { (inj₁ f) → proxy≢client (link-confined proxy f)
  ; (inj₂ f) → target≢client (link-confined target f) }
  where
  proxy≢client : proxy ≢ client
  proxy≢client ()
  target≢client : target ≢ client
  target≢client ()
