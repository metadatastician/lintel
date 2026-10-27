{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
--
-- The reader-set lattice as an instance of secret-types' Lattice record, and
-- secret-types' generic TINI at it (README L-6).
--
--   reader-sets      the instance: Lintel.Lattice's ⊑, ⊔, anyone and the
--                    three laws the census needs (⊑-trans, ⊔-upper₁, ⊔-upper₂)
--   fields           the variables: the address, the query name, and the
--                    client's local state
--   field-label      address, qname, and the client alone
--   tini-per-role    TINI for each role's principal observer
--   tini-coalition   TINI for any two roles observing together
--   collusion-gap    why A-1 stays: a coalition of proxy and target sees each
--                    field, though not their composition
--   coalition-blind  ... nor the client's local state, so coalition TINI
--                    relates stores that differ there
--
-- Pin: hyperpolymath/secret-types ee01db4dc34e457cbc32cfb1b7abd737ea8f075a
--   SecretTypes.Vars, SecretTypes.Lang, SecretTypes.Lattice.Record,
--   SecretTypes.Noninterference.Generic (scripts/fetch-siblings.sh)
module Lintel.Instance where

open import SecretTypes.Prelude
open import SecretTypes.Vars
open import SecretTypes.Lattice.Record
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

----------------------------------------------------------------------
-- The variables of a program handling one oblivious query: the client's
-- address, the query name, and the client's local state, where the client
-- may keep what only it may know.

data Field : Set where
  addr qn local : Field

infix 4 _≟f_
-- Decide equality of fields.
_≟f_ : (x y : Field) → Dec (x ≡ y)
addr  ≟f addr  = yes refl
addr  ≟f qn    = no λ ()
addr  ≟f local = no λ ()
qn    ≟f addr  = no λ ()
qn    ≟f qn    = yes refl
qn    ≟f local = no λ ()
local ≟f addr  = no λ ()
local ≟f qn    = no λ ()
local ≟f local = yes refl

fields : Vars
fields = record { Var = Field ; _≟ᵥ_ = _≟f_ }

open import SecretTypes.Lang fields public

field-label : Field → Label
field-label addr  = address
field-label qn    = qname
field-label local = observer client

open import SecretTypes.Noninterference.Generic fields reader-sets field-label public

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

-- The composite label is the client's local state's label (link), so the
-- coalition does not see that variable either.
coalition-blind : ¬ Observer.sees (coalition proxy target) (field-label local)
coalition-blind = snd (snd collusion-gap)

-- So coalition TINI is not determinism in disguise: it relates two stores
-- that differ in the client's local state, and says the runs end agreeing
-- on the address and the query name whatever that state was.
store₀ store₁ : Store
store₀ _     = 0
store₁ addr  = 0
store₁ qn    = 0
store₁ local = 1

coalition-agrees : store₀ ≈[ Observer.sees (coalition proxy target) ] store₁
coalition-agrees addr  _ = refl
coalition-agrees qn    _ = refl
coalition-agrees local v = ⊥-elim (coalition-blind v)

stores-differ : read store₀ local ≢ read store₁ local
stores-differ ()
