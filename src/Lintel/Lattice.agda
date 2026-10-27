{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
--
-- Lintel's privacy lattice.  A label is the set of oblivious-DNS roles that
-- may observe a datum.  Labels are attached per field (owner decision
-- 2026-10-14, LNT-01): the client's address and the query name are separate
-- fields with separate labels, and the roles are the observers.
--
--   ℓ ⊑ ℓ'    a datum labelled ℓ may flow to ℓ': every role that may observe
--             ℓ' may already observe ℓ (reverse inclusion of reader sets)
--   ℓ ⊔ ℓ'    combining two fields: the roles that may observe both
--   ℓ ⊓ ℓ'    the roles that may observe either
--   anyone    bottom: every role may observe
--   no-one    top: no role may observe; it never flows down
--
-- Every pair of labels has a join and a meet, so this is a lattice (reader
-- sets over three roles: eight labels), not a poset completed by hand.  The
-- laws are proved here as lemmas; Lintel.Instance packs them into
-- secret-types' Lattice record (SecretTypes.Lattice.Record,
-- hyperpolymath/secret-types#9).  No second definition of the record is made
-- here.
--
-- Pins:
--   hyperpolymath/secret-types   ee01db4dc34e457cbc32cfb1b7abd737ea8f075a
--     SecretTypes.Prelude, imported (scripts/fetch-siblings.sh)
--   hyperpolymath/proven-servers b58289e7862139efd918561a7ddc9cb5605ea9d8
--     protocols/proven-odns/src/ODNS/Types.idr, Role = Client | Proxy | Target;
--     Idris2, so transcribed here, not imported
module Lintel.Lattice where

open import Agda.Builtin.Bool using (Bool; true; false)
open import SecretTypes.Prelude

----------------------------------------------------------------------
-- Roles and labels

data Role : Set where
  client proxy target : Role

-- One bit per role: may that role observe the datum?
record Label : Set where
  constructor ⟨_,_,_⟩
  field
    by-client by-proxy by-target : Bool
open Label public

-- May role r observe a datum labelled ℓ?
reads : Label → Role → Bool
reads ℓ client = by-client ℓ
reads ℓ proxy  = by-proxy ℓ
reads ℓ target = by-target ℓ

anyone no-one : Label
anyone = ⟨ true , true , true ⟩
no-one = ⟨ false , false , false ⟩

----------------------------------------------------------------------
-- Flow, one bit at a time

-- a ⊒ b: every reader b admits, a admits too (b implies a).
infix 4 _⊒_
data _⊒_ : Bool → Bool → Set where
  ⊒-true  : ∀ {b} → true ⊒ b
  ⊒-false : false ⊒ false

infix 4 _⊑_
record _⊑_ (ℓ ℓ' : Label) : Set where
  constructor flows
  field
    at-client : by-client ℓ ⊒ by-client ℓ'
    at-proxy  : by-proxy  ℓ ⊒ by-proxy  ℓ'
    at-target : by-target ℓ ⊒ by-target ℓ'
open _⊑_ public

infixr 6 _∧_
infixr 5 _∨_
_∧_ _∨_ : Bool → Bool → Bool
true  ∧ b = b
false ∧ _ = false
true  ∨ _ = true
false ∨ b = b

infixl 6 _⊔_
infixl 7 _⊓_
_⊔_ _⊓_ : Label → Label → Label
ℓ ⊔ ℓ' = ⟨ by-client ℓ ∧ by-client ℓ' , by-proxy ℓ ∧ by-proxy ℓ' , by-target ℓ ∧ by-target ℓ' ⟩
ℓ ⊓ ℓ' = ⟨ by-client ℓ ∨ by-client ℓ' , by-proxy ℓ ∨ by-proxy ℓ' , by-target ℓ ∨ by-target ℓ' ⟩

----------------------------------------------------------------------
-- Bit lemmas

⊒-refl : ∀ b → b ⊒ b
⊒-refl true  = ⊒-true
⊒-refl false = ⊒-false

⊒-trans : ∀ {a b c} → a ⊒ b → b ⊒ c → a ⊒ c
⊒-trans ⊒-true  _       = ⊒-true
⊒-trans ⊒-false ⊒-false = ⊒-false

⊒-antisym : ∀ {a b} → a ⊒ b → b ⊒ a → a ≡ b
⊒-antisym ⊒-true  ⊒-true  = refl
⊒-antisym ⊒-false ⊒-false = refl

-- Every bit admits at least what a closed bit admits.
⊒-closed : ∀ b → b ⊒ false
⊒-closed true  = ⊒-true
⊒-closed false = ⊒-false

∧-left : ∀ a b → a ⊒ a ∧ b
∧-left true  _ = ⊒-true
∧-left false _ = ⊒-false

∧-right : ∀ a b → b ⊒ a ∧ b
∧-right true  b = ⊒-refl b
∧-right false b = ⊒-closed b

∧-greatest : ∀ {a b c} → a ⊒ c → b ⊒ c → a ∧ b ⊒ c
∧-greatest ⊒-true  q = q
∧-greatest ⊒-false _ = ⊒-false

∨-left : ∀ a b → a ∨ b ⊒ a
∨-left true  _ = ⊒-true
∨-left false b = ⊒-closed b

∨-right : ∀ a b → a ∨ b ⊒ b
∨-right true  _ = ⊒-true
∨-right false b = ⊒-refl b

∨-least : ∀ {a b c} → c ⊒ a → c ⊒ b → c ⊒ a ∨ b
∨-least ⊒-true  _       = ⊒-true
∨-least ⊒-false ⊒-false = ⊒-false

∧-true₁ : ∀ a b → a ∧ b ≡ true → a ≡ true
∧-true₁ true  _ _ = refl
∧-true₁ false _ ()

∧-true₂ : ∀ a b → a ∧ b ≡ true → b ≡ true
∧-true₂ true  _ e = e
∧-true₂ false _ ()

----------------------------------------------------------------------
-- The order is a partial order

⊑-refl : ∀ ℓ → ℓ ⊑ ℓ
⊑-refl ℓ = flows (⊒-refl (by-client ℓ)) (⊒-refl (by-proxy ℓ)) (⊒-refl (by-target ℓ))

⊑-trans : ∀ {ℓ₁ ℓ₂ ℓ₃} → ℓ₁ ⊑ ℓ₂ → ℓ₂ ⊑ ℓ₃ → ℓ₁ ⊑ ℓ₃
⊑-trans (flows c p t) (flows c' p' t') = flows (⊒-trans c c') (⊒-trans p p') (⊒-trans t t')

⊑-antisym : ∀ {ℓ ℓ'} → ℓ ⊑ ℓ' → ℓ' ⊑ ℓ → ℓ ≡ ℓ'
⊑-antisym {⟨ _ , _ , _ ⟩} {⟨ _ , _ , _ ⟩} (flows c p t) (flows c' p' t')
  with ⊒-antisym c c' | ⊒-antisym p p' | ⊒-antisym t t'
... | refl | refl | refl = refl

-- The bit encoding means exactly reverse inclusion of reader sets.
⊒-sound : ∀ {a b} → a ⊒ b → b ≡ true → a ≡ true
⊒-sound ⊒-true  _ = refl
⊒-sound ⊒-false ()

⊒-complete : ∀ a b → (b ≡ true → a ≡ true) → a ⊒ b
⊒-complete true  _     _ = ⊒-true
⊒-complete false false _ = ⊒-false
⊒-complete false true  h with h refl
... | ()

⊑-readers : ∀ {ℓ ℓ'} → ℓ ⊑ ℓ' → ∀ r → reads ℓ' r ≡ true → reads ℓ r ≡ true
⊑-readers f client = ⊒-sound (at-client f)
⊑-readers f proxy  = ⊒-sound (at-proxy f)
⊑-readers f target = ⊒-sound (at-target f)

readers-⊑ : ∀ ℓ ℓ' → (∀ r → reads ℓ' r ≡ true → reads ℓ r ≡ true) → ℓ ⊑ ℓ'
readers-⊑ ℓ ℓ' h =
  flows (⊒-complete (by-client ℓ) (by-client ℓ') (h client))
        (⊒-complete (by-proxy ℓ)  (by-proxy ℓ')  (h proxy))
        (⊒-complete (by-target ℓ) (by-target ℓ') (h target))

----------------------------------------------------------------------
-- Joins, meets, bounds: a lattice

⊔-upper₁ : ∀ ℓ ℓ' → ℓ ⊑ ℓ ⊔ ℓ'
⊔-upper₁ ℓ ℓ' = flows (∧-left (by-client ℓ) (by-client ℓ'))
                      (∧-left (by-proxy ℓ)  (by-proxy ℓ'))
                      (∧-left (by-target ℓ) (by-target ℓ'))

⊔-upper₂ : ∀ ℓ ℓ' → ℓ' ⊑ ℓ ⊔ ℓ'
⊔-upper₂ ℓ ℓ' = flows (∧-right (by-client ℓ) (by-client ℓ'))
                      (∧-right (by-proxy ℓ)  (by-proxy ℓ'))
                      (∧-right (by-target ℓ) (by-target ℓ'))

⊔-least : ∀ {ℓ₁ ℓ₂ ℓ} → ℓ₁ ⊑ ℓ → ℓ₂ ⊑ ℓ → ℓ₁ ⊔ ℓ₂ ⊑ ℓ
⊔-least (flows c p t) (flows c' p' t') = flows (∧-greatest c c') (∧-greatest p p') (∧-greatest t t')

⊓-lower₁ : ∀ ℓ ℓ' → ℓ ⊓ ℓ' ⊑ ℓ
⊓-lower₁ ℓ ℓ' = flows (∨-left (by-client ℓ) (by-client ℓ'))
                      (∨-left (by-proxy ℓ)  (by-proxy ℓ'))
                      (∨-left (by-target ℓ) (by-target ℓ'))

⊓-lower₂ : ∀ ℓ ℓ' → ℓ ⊓ ℓ' ⊑ ℓ'
⊓-lower₂ ℓ ℓ' = flows (∨-right (by-client ℓ) (by-client ℓ'))
                      (∨-right (by-proxy ℓ)  (by-proxy ℓ'))
                      (∨-right (by-target ℓ) (by-target ℓ'))

⊓-greatest : ∀ {ℓ ℓ₁ ℓ₂} → ℓ ⊑ ℓ₁ → ℓ ⊑ ℓ₂ → ℓ ⊑ ℓ₁ ⊓ ℓ₂
⊓-greatest (flows c p t) (flows c' p' t') = flows (∨-least c c') (∨-least p p') (∨-least t t')

anyone-least : ∀ ℓ → anyone ⊑ ℓ
anyone-least _ = flows ⊒-true ⊒-true ⊒-true

no-one-greatest : ∀ ℓ → ℓ ⊑ no-one
no-one-greatest ℓ = flows (⊒-closed (by-client ℓ)) (⊒-closed (by-proxy ℓ)) (⊒-closed (by-target ℓ))

-- The top never flows down (⊤ ⋢ ⊥).
no-one-⋢-anyone : ¬ (no-one ⊑ anyone)
no-one-⋢-anyone (flows () _ _)

----------------------------------------------------------------------
-- The two-point laws secret-types' TINI proof used before its census
-- (the 2026-10-12 reading of PROOF-STATUS N-6), stated for this one: L
-- becomes anyone, H no-one.  The certified census (N-6 since ccdcb3e) needs
-- only ⊔-upper₁, ⊔-upper₂ and ⊑-trans above; these stay as facts.

-- L ⊔ y = y
anyone-⊔ : ∀ ℓ → anyone ⊔ ℓ ≡ ℓ
anyone-⊔ ⟨ _ , _ , _ ⟩ = refl

-- H ⊔ y = H
no-one-⊔ : ∀ ℓ → no-one ⊔ ℓ ≡ no-one
no-one-⊔ _ = refl

-- ⊔-L₁: a join everyone may observe has a left part everyone may observe.
⊔-anyone₁ : ∀ {ℓ ℓ'} → ℓ ⊔ ℓ' ≡ anyone → ℓ ≡ anyone
⊔-anyone₁ {⟨ c , p , t ⟩} {ℓ'} e
  with ∧-true₁ c (by-client ℓ') (cong by-client e)
    | ∧-true₁ p (by-proxy ℓ')  (cong by-proxy e)
    | ∧-true₁ t (by-target ℓ') (cong by-target e)
... | refl | refl | refl = refl

-- ⊔-L₂: and a right part everyone may observe.
⊔-anyone₂ : ∀ {ℓ ℓ'} → ℓ ⊔ ℓ' ≡ anyone → ℓ' ≡ anyone
⊔-anyone₂ {ℓ} {⟨ c , p , t ⟩} e
  with ∧-true₂ (by-client ℓ) c (cong by-client e)
    | ∧-true₂ (by-proxy ℓ)  p (cong by-proxy e)
    | ∧-true₂ (by-target ℓ) t (cong by-target e)
... | refl | refl | refl = refl

----------------------------------------------------------------------
-- Decidable flow (Dec from SecretTypes.Prelude)

_⊒?_ : ∀ a b → Dec (a ⊒ b)
true  ⊒? _     = yes ⊒-true
false ⊒? false = yes ⊒-false
false ⊒? true  = no λ ()

_⊑?_ : ∀ ℓ ℓ' → Dec (ℓ ⊑ ℓ')
ℓ ⊑? ℓ' with by-client ℓ ⊒? by-client ℓ' | by-proxy ℓ ⊒? by-proxy ℓ' | by-target ℓ ⊒? by-target ℓ'
... | yes c | yes p | yes t = yes (flows c p t)
... | no ¬c | _     | _     = no λ f → ¬c (at-client f)
... | yes _ | no ¬p | _     = no λ f → ¬p (at-proxy f)
... | yes _ | yes _ | no ¬t = no λ f → ¬t (at-target f)

----------------------------------------------------------------------
-- Observers.  Role r's observation level is the label only r may observe;
-- r sees a datum exactly when the datum may flow to that level.  This is
-- the shape TINI's low observer takes at this lattice: one observer per
-- role.  A party holding two roles is a coalition, not one of these
-- observers: Lintel.Instance covers it for TINI, and shows why it still
-- defeats the link.

observer : Role → Label
observer client = ⟨ true , false , false ⟩
observer proxy  = ⟨ false , true , false ⟩
observer target = ⟨ false , false , true ⟩

observes-flow : ∀ ℓ r → reads ℓ r ≡ true → ℓ ⊑ observer r
observes-flow ⟨ _ , p , t ⟩ client refl = flows ⊒-true (⊒-closed p) (⊒-closed t)
observes-flow ⟨ c , _ , t ⟩ proxy  refl = flows (⊒-closed c) ⊒-true (⊒-closed t)
observes-flow ⟨ c , p , _ ⟩ target refl = flows (⊒-closed c) (⊒-closed p) ⊒-true

flow-observes : ∀ ℓ r → ℓ ⊑ observer r → reads ℓ r ≡ true
flow-observes ℓ client f = ⊒-sound (at-client f) refl
flow-observes ℓ proxy  f = ⊒-sound (at-proxy f) refl
flow-observes ℓ target f = ⊒-sound (at-target f) refl

----------------------------------------------------------------------
-- Two fields of an oblivious query.
--   address  the client's network address: the client and the proxy see it
--   qname    the query name: the client and the target see it

address qname : Label
address = ⟨ true , true , false ⟩
qname   = ⟨ true , false , true ⟩

-- Each field alone reaches the role that handles it ...
address-to-proxy : address ⊑ observer proxy
address-to-proxy = flows ⊒-true ⊒-true ⊒-false

qname-to-target : qname ⊑ observer target
qname-to-target = flows ⊒-true ⊒-false ⊒-true

-- ... but composing them gives a label only the client may observe.
link : address ⊔ qname ≡ observer client
link = refl

link-to-client : address ⊔ qname ⊑ observer client
link-to-client = flows ⊒-true ⊒-false ⊒-false

-- No role but the client may observe the composition.
link-confined : ∀ r → address ⊔ qname ⊑ observer r → r ≡ client
link-confined client _ = refl
link-confined proxy  (flows _ () _)
link-confined target (flows _ _ ())
