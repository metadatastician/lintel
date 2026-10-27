{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
--
-- Self-defeating compositions cannot be built as programs (README L-7).
-- L-4 says the label address ⊔ qname reaches only the client.  Here that is
-- carried to commands typed by secret-types' rules at this lattice: no
-- well-typed command writes a value depending on both fields, explicitly
-- (through its expression) or implicitly (through the guards it sits
-- under), anywhere a role other than the client may read it.
--
--   Writes x k c             c contains an assignment to x whose value
--                            depends on data labelled k: the expression and
--                            every enclosing guard
--   writes-flow              in a typed command, the counter and k both flow
--                            to x
--   link-written-to-client   for any variables and labelling: the link is
--                            written only where the client alone may read it
--   link-written-to-local    for Lintel's fields: it is written only into the
--                            client's local state
--   link-writable            and it can be written there, so the refusal is
--                            not a refusal of everything
--
-- Pin: hyperpolymath/secret-types ee01db4dc34e457cbc32cfb1b7abd737ea8f075a
--   SecretTypes.Vars, SecretTypes.Lang, SecretTypes.Typing.Generic
--   (scripts/fetch-siblings.sh)
module Lintel.Composition where

open import SecretTypes.Prelude
open import SecretTypes.Vars
open import Lintel.Lattice
open import Lintel.Instance as I using (fields; field-label; addr; qn; local)

module _ (𝓥 : Vars) (label : Vars.Var 𝓥 → Label) where
  open import SecretTypes.Lang 𝓥 using (Var; Expr; Cmd; _≔_; _﹔_; ifz; while)
  open import SecretTypes.Typing.Generic 𝓥 _⊑_ _⊔_ anyone label

  -- Which data an assignment inside c depends on.  The guards an assignment
  -- sits under are joined into k, so implicit flows count as dependence.
  data Writes (x : Var) : Label → Cmd → Set where
    here  : ∀ {e} → Writes x (lab e) (x ≔ e)
    seq₁  : ∀ {k c₁ c₂} → Writes x k c₁ → Writes x k (c₁ ﹔ c₂)
    seq₂  : ∀ {k c₁ c₂} → Writes x k c₂ → Writes x k (c₁ ﹔ c₂)
    ifz₁  : ∀ {k g c₁ c₂} → Writes x k c₁ → Writes x (lab g ⊔ k) (ifz g c₁ c₂)
    ifz₂  : ∀ {k g c₁ c₂} → Writes x k c₂ → Writes x (lab g ⊔ k) (ifz g c₁ c₂)
    body  : ∀ {k g c} → Writes x k c → Writes x (lab g ⊔ k) (while g c)

  -- A guard's label joins what the writes beneath it depend on.
  private
    under-guard : ∀ pc g {x k} → (pc ⊔ lab g) ⊑ label x × k ⊑ label x
                → pc ⊑ label x × (lab g ⊔ k) ⊑ label x
    under-guard pc g (p , q) =
      ⊑-trans (⊔-upper₁ pc (lab g)) p , ⊔-least (⊑-trans (⊔-upper₂ pc (lab g)) p) q

  -- Every write in a typed command is a permitted flow: from the counter,
  -- and from everything the written value depends on.  The counter half is
  -- the induction hypothesis the guard cases need.
  writes-flow : ∀ {pc c x k} → pc ⊢ c → Writes x k c → pc ⊑ label x × k ⊑ label x
  writes-flow {pc} (assign {e = e} ok) here =
    ⊑-trans (⊔-upper₁ pc (lab e)) ok , ⊑-trans (⊔-upper₂ pc (lab e)) ok
  writes-flow (seq t₁ _) (seq₁ w) = writes-flow t₁ w
  writes-flow (seq _ t₂) (seq₂ w) = writes-flow t₂ w
  writes-flow {pc} (ifz {e = g} t₁ _) (ifz₁ w) = under-guard pc g (writes-flow t₁ w)
  writes-flow {pc} (ifz {e = g} _ t₂) (ifz₂ w) = under-guard pc g (writes-flow t₂ w)
  writes-flow {pc} (while {e = g} t) (body w) = under-guard pc g (writes-flow t w)

  -- A write that depends on both fields lands only where the client alone
  -- may read it, whatever the variables and their labelling.
  link-written-to-client : ∀ {pc c x k} r → pc ⊢ c → Writes x k c → address ⊔ qname ⊑ pc ⊔ k
                 → label x ⊑ observer r → r ≡ client
  link-written-to-client {pc} r t w h obs with writes-flow t w
  ... | p , q = link-confined r (⊑-trans h (⊑-trans (⊔-least p q) obs))

-- With Lintel's fields as the variables, the address is the proxy's too and
-- the query name the target's, so the link is written only into the
-- client's local state.
link-written-to-local : ∀ {pc c x k} → pc I.⊢ c → Writes fields field-label x k c
                      → address ⊔ qname ⊑ pc ⊔ k → x ≡ local
link-written-to-local {x = addr} t w h with link-written-to-client fields field-label proxy t w h address-to-proxy
... | ()
link-written-to-local {x = qn} t w h with link-written-to-client fields field-label target t w h qname-to-target
... | ()
link-written-to-local {x = local} _ _ _ = refl

-- The client may compose its own address and query name into its local
-- state: a typed command that writes the link, so link-written-to-local is
-- not vacuous.
link-writable : Σ I.Cmd λ c → anyone I.⊢ c × Writes fields field-label local (address ⊔ qname) c
link-writable = (local I.≔ I.plus (I.var addr) (I.var qn)) , (I.assign (flows ⊒-true ⊒-false ⊒-false) , here)
