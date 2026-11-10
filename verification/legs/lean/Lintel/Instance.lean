/-
SPDX-License-Identifier: MPL-2.0
SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

Lean leg (PROOF-POLICY §2, route `re-proved`) of Lintel L-6 and the proved
half of A-1: src/Lintel/Instance.agda, statement by statement.

The record and the theorem are secret-types', imported from its own Lean
leg (`SecretTypes.Lattice`, `SecretTypes.tini`) at the pin, exactly as the
Agda module imports `SecretTypes.Lattice.Record` and
`SecretTypes.Noninterference.Generic`.  Nothing of secret-types is restated.
-/
import SecretTypes.Generic
import Lintel.Lattice

namespace Lintel
open SecretTypes

/-! The instance.  The record is secret-types'; only the fields are Lintel's. -/

def readerSets : Lattice where
  Carrier := Label
  le := Le
  join := join
  bot := anyone
  le_trans := le_trans
  upper₁ := upper₁
  upper₂ := upper₂

/-! The variables of a program handling one oblivious query: the client's
address, the query name, and the client's local state.  (`local` is a Lean
keyword, hence `«local»`.) -/

inductive Field where
  | addr | qn | «local»

/-- `_≟f_`: decide equality of fields, clause by clause. -/
def fieldDeq : (x y : Field) → Decidable (x = y)
  | .addr, .addr => .isTrue rfl
  | .addr, .qn => .isFalse (fun h => nomatch h)
  | .addr, .«local» => .isFalse (fun h => nomatch h)
  | .qn, .addr => .isFalse (fun h => nomatch h)
  | .qn, .qn => .isTrue rfl
  | .qn, .«local» => .isFalse (fun h => nomatch h)
  | .«local», .addr => .isFalse (fun h => nomatch h)
  | .«local», .qn => .isFalse (fun h => nomatch h)
  | .«local», .«local» => .isTrue rfl

def fields : Vars := ⟨Field, fieldDeq⟩

/-- Label the address for client and proxy, the query name for client and
target, and local state for the client alone. -/
def fieldLabel : fields.Var → readerSets.Carrier
  | .addr => address
  | .qn => qname
  | .«local» => observer .client

/-! L-6: one principal observer per role. -/

def role (r : Role) : Observer readerSets := principal readerSets (observer r)

theorem tini_per_role (r : Role) :
    TINI readerSets.toSignature fieldLabel (role r).sees :=
  tini (label := fieldLabel) (role r)

/-! Coalitions.  A union of down-closed observers is down-closed, over any
lattice. -/

/-- Observe a label when either observer sees it, retaining which observer
supplied the witness. Downward closure preserves that choice. -/
def union {L : Lattice} (V W : Observer L) : Observer L where
  sees l := Sum (V.sees l) (W.sees l)
  down p
    | .inl v => .inl (V.down p v)
    | .inr w => .inr (W.down p w)

/-- Observe labels visible to either role individually. This does not grant
visibility of a joined label merely because each role sees one component. -/
def coalition (r r' : Role) : Observer readerSets := union (role r) (role r')

theorem tini_coalition (r r' : Role) :
    TINI readerSets.toSignature fieldLabel (coalition r r').sees :=
  tini (label := fieldLabel) (coalition r r')

/-- `collusion-gap`: proxy and target together see each field, but not their
composition.  Agda's `_×_` of two `Set`s and a negation; `PProd` here,
because the negation is a proposition. -/
def collusion_gap :
    PProd ((coalition .proxy .target).sees address)
      (PProd ((coalition .proxy .target).sees qname)
        ((coalition .proxy .target).sees (join address qname) → False)) :=
  ⟨.inl address_to_proxy, .inr qname_to_target, fun
    | .inl f => nomatch link_confined .proxy f
    | .inr f => nomatch link_confined .target f⟩

theorem coalition_blind : (coalition .proxy .target).sees (fieldLabel .«local») → False :=
  collusion_gap.2.2

def store₀ : Store fields := fun _ => 0

def store₁ : Store fields
  | .addr => 0
  | .qn => 0
  | .«local» => 1

theorem coalition_agrees :
    Agree readerSets.toSignature fieldLabel (coalition .proxy .target).sees store₀ store₁
  | .addr, _ => rfl
  | .qn, _ => rfl
  | .«local», v => (coalition_blind v).elim

theorem stores_differ : store₀ .«local» ≠ store₁ .«local» := fun h => nomatch h

end Lintel
