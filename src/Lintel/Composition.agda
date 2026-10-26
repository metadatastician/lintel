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
--   link-written-to-client   for any labelling of the variables: the link is
--                            written only where the client alone may read it
--   no-link-written          for Lintel's fields: it is written nowhere
--
-- Pin: hyperpolymath/secret-types ccdcb3ec42792337a9ab6047e1f99de9d20a4f96
--   SecretTypes.Typing.Generic (scripts/fetch-siblings.sh)
module Lintel.Composition where

open import SecretTypes.Prelude
open import SecretTypes.Lang using (Var; lo; hi; Expr; Cmd; _≔_; _﹔_; ifz; while)
open import Lintel.Lattice
open import Lintel.Instance as I using (field-label)

module _ (label : Var → Label) where
  open import SecretTypes.Typing.Generic _⊑_ _⊔_ anyone label

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
  -- may read it, whatever the labelling.
  link-written-to-client : ∀ {pc c x k} r → pc ⊢ c → Writes x k c → address ⊔ qname ⊑ pc ⊔ k
                 → label x ⊑ observer r → r ≡ client
  link-written-to-client {pc} r t w h obs with writes-flow t w
  ... | p , q = link-confined r (⊑-trans h (⊑-trans (⊔-least p q) obs))

-- With Lintel's two fields as the variables, no variable is the client's
-- alone: the address is the proxy's too, the query name the target's.  So
-- no typed command writes the link anywhere.
no-link-written : ∀ {pc c x k} → pc I.⊢ c → Writes field-label x k c
                → address ⊔ qname ⊑ pc ⊔ k → ⊥
no-link-written {x = lo} t w h with link-written-to-client field-label proxy t w h address-to-proxy
... | ()
no-link-written {x = hi} t w h with link-written-to-client field-label target t w h qname-to-target
... | ()
