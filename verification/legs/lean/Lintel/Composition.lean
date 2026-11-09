/-
SPDX-License-Identifier: MPL-2.0
SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

Lean leg (PROOF-POLICY §2, route `re-proved`) of Lintel L-7:
src/Lintel/Composition.agda, statement by statement.  Commands and their
typing are secret-types' (`SecretTypes.Cmd`, `SecretTypes.Typed`), at the
reader-set signature, as the Agda module opens
`SecretTypes.Typing.Generic 𝓥 _⊑_ _⊔_ anyone label`.

The Agda proof of `writes-flow` reads `Writes` into `Writes′`, a relation
computed by recursion on the command, because matching a typing derivation
and a `Writes` derivation together needs constructor injectivity, which
`--cubical-compatible` refuses.  Lean has no such restriction, so this leg
matches the two together.  The statements are the same; only the proof
route differs, and `Writes′` is private in Agda, so no statement mentions it.
-/
import SecretTypes.Generic
import Lintel.Lattice
import Lintel.Instance

namespace Lintel
open SecretTypes

/-- The signature `SecretTypes.Typing.Generic` is opened at: `_⊑_`, `_⊔_`,
`anyone`.  It is the signature underneath `readerSets`. -/
abbrev readerSig : Signature := readerSets.toSignature

section Generic
variable {V : Vars} (label : V.Var → Label)

/-- Which data an assignment inside `c` depends on.  The guards an
assignment sits under are joined into `k`, so implicit flows count. -/
inductive Writes (x : V.Var) : Label → Cmd V → Type where
  | here {e} : Writes x (lab readerSig label e) (.assign x e)
  | seq₁ {k c₁ c₂} : Writes x k c₁ → Writes x k (.seq c₁ c₂)
  | seq₂ {k c₁ c₂} : Writes x k c₂ → Writes x k (.seq c₁ c₂)
  | ifz₁ {k g c₁ c₂} : Writes x k c₁ → Writes x (join (lab readerSig label g) k) (.ifz g c₁ c₂)
  | ifz₂ {k g c₁ c₂} : Writes x k c₂ → Writes x (join (lab readerSig label g) k) (.ifz g c₁ c₂)
  | body {k g c} : Writes x k c → Writes x (join (lab readerSig label g) k) (.«while» g c)

/-- A guard's label joins what the writes beneath it depend on. -/
def under_guard {x : V.Var} {k : Label} (pc : Label) (g : Expr V)
    (h : Le (join pc (lab readerSig label g)) (label x) × Le k (label x)) :
    Le pc (label x) × Le (join (lab readerSig label g) k) (label x) :=
  ⟨le_trans (upper₁ pc _) h.1, join_least (le_trans (upper₂ pc _) h.1) h.2⟩

/-- `writes-flow`: every write in a typed command is a permitted flow, from
the counter and from everything the written value depends on. -/
def writes_flow : ∀ {pc : Label} {c : Cmd V} {x : V.Var} {k : Label},
    Typed readerSig label pc c → Writes label x k c → Le pc (label x) × Le k (label x)
  | _, .skip, _, _, _, w => nomatch w
  | pc, _, _, _, .assign ok, .here => ⟨le_trans (upper₁ pc _) ok, le_trans (upper₂ pc _) ok⟩
  | _, _, _, _, .seq t₁ _, .seq₁ w => writes_flow t₁ w
  | _, _, _, _, .seq _ t₂, .seq₂ w => writes_flow t₂ w
  | pc, .ifz g _ _, _, _, .ifz t₁ _, .ifz₁ w => under_guard label pc g (writes_flow t₁ w)
  | pc, .ifz g _ _, _, _, .ifz _ t₂, .ifz₂ w => under_guard label pc g (writes_flow t₂ w)
  | pc, .«while» g _, _, _, .«while» t, .body w => under_guard label pc g (writes_flow t w)

/-- `link-written-to-client`: a write that depends on both fields lands only
where the client alone may read it, whatever the variables and labelling. -/
theorem link_written_to_client {pc : Label} {c : Cmd V} {x : V.Var} {k : Label} (r : Role)
    (t : Typed readerSig label pc c) (w : Writes label x k c)
    (h : Le (join address qname) (join pc k)) (obs : Le (label x) (observer r)) :
    r = .client :=
  let pq := writes_flow label t w
  link_confined r (le_trans h (le_trans (join_least pq.1 pq.2) obs))

end Generic

/-- `link-written-to-local`: with Lintel's fields, the link is written only
into the client's local state. -/
theorem link_written_to_local : ∀ {pc : Label} {c : Cmd fields} {x : Field} {k : Label},
    Typed readerSig fieldLabel pc c → Writes fieldLabel x k c →
    Le (join address qname) (join pc k) → x = .«local»
  | _, _, .addr, _, t, w, h =>
      nomatch link_written_to_client fieldLabel .proxy t w h address_to_proxy
  | _, _, .qn, _, t, w, h =>
      nomatch link_written_to_client fieldLabel .target t w h qname_to_target
  | _, _, .«local», _, _, _, _ => rfl

/-- `link-writable`: the client may compose its own address and query name
into its local state, so `link_written_to_local` is not vacuous. -/
def link_writable :
    (c : Cmd fields) × (Typed readerSig fieldLabel anyone c ×
      Writes fieldLabel Field.«local» (join address qname) c) :=
  ⟨.assign .«local» (.plus (.var .addr) (.var .qn)), .assign ⟨.tru, .fls, .fls⟩,
    @Writes.here fields fieldLabel .«local» (.plus (.var .addr) (.var .qn))⟩

end Lintel
