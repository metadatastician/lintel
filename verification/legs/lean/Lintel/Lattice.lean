/-
SPDX-License-Identifier: MPL-2.0
SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

Lean leg (PROOF-POLICY §2, route `re-proved`) of Lintel L-1, L-2, L-3 and
L-4: src/Lintel/Lattice.agda, statement by statement.  Lean core only.

Universe discipline: Agda's `Set` is `Type`.  The bit order `_⊒_` and the
label order `_⊑_` are `Type`-valued, as in Agda, so a flow proof is data.
Equalities are `Prop`; they are equalities of booleans, labels and roles,
all decidable, so the two readings hold the same information.
-/
namespace Lintel

/-! Roles and labels -/

inductive Role where
  | client | proxy | target

/-- One bit per role: may that role observe the datum? -/
structure Label where
  byClient : Bool
  byProxy : Bool
  byTarget : Bool

/-- May role `r` observe a datum labelled `l`? -/
def reads (l : Label) : Role → Bool
  | .client => l.byClient
  | .proxy => l.byProxy
  | .target => l.byTarget

def anyone : Label := ⟨true, true, true⟩
def noOne : Label := ⟨false, false, false⟩

/-! Flow, one bit at a time -/

/-- `a ⊒ b`: every reader `b` admits, `a` admits too. -/
inductive Ge : Bool → Bool → Type where
  | tru {b : Bool} : Ge true b
  | fls : Ge false false

/-- `ℓ ⊑ ℓ'`, the record `_⊑_` with constructor `flows`. -/
structure Le (l l' : Label) : Type where
  atClient : Ge l.byClient l'.byClient
  atProxy : Ge l.byProxy l'.byProxy
  atTarget : Ge l.byTarget l'.byTarget

/-- `_∧_` and `_∨_` of `Lintel.Lattice`, defined by the same clauses. -/
def band : Bool → Bool → Bool
  | true, b => b
  | false, _ => false

def bor : Bool → Bool → Bool
  | true, _ => true
  | false, b => b

/-- `ℓ ⊔ ℓ'`: the roles that may observe both. -/
def join (l l' : Label) : Label :=
  ⟨band l.byClient l'.byClient, band l.byProxy l'.byProxy, band l.byTarget l'.byTarget⟩

/-- `ℓ ⊓ ℓ'`: the roles that may observe either. -/
def meet (l l' : Label) : Label :=
  ⟨bor l.byClient l'.byClient, bor l.byProxy l'.byProxy, bor l.byTarget l'.byTarget⟩

/-! Bit lemmas -/

def ge_refl : ∀ b, Ge b b
  | true => .tru
  | false => .fls

def ge_trans : ∀ {a b c}, Ge a b → Ge b c → Ge a c
  | _, _, _, .tru, _ => .tru
  | _, _, _, .fls, q => q

theorem ge_open : ∀ {a}, Ge a true → a = true
  | _, .tru => rfl

theorem ge_antisym : ∀ {a b}, Ge a b → Ge b a → a = b
  | _, _, .tru, q => (ge_open q).symm
  | _, _, .fls, _ => rfl

def ge_closed : ∀ b, Ge b false
  | true => .tru
  | false => .fls

def and_left : ∀ a b, Ge a (band a b)
  | true, _ => .tru
  | false, _ => .fls

def and_right : ∀ a b, Ge b (band a b)
  | true, b => ge_refl b
  | false, b => ge_closed b

def and_greatest : ∀ {a b c}, Ge a c → Ge b c → Ge (band a b) c
  | _, _, _, .tru, q => q
  | _, _, _, .fls, _ => .fls

def or_left : ∀ a b, Ge (bor a b) a
  | true, _ => .tru
  | false, b => ge_closed b

def or_right : ∀ a b, Ge (bor a b) b
  | true, _ => .tru
  | false, b => ge_refl b

def or_least : ∀ {a b c}, Ge c a → Ge c b → Ge c (bor a b)
  | _, _, _, .tru, _ => .tru
  | _, _, _, .fls, q => q

theorem and_true₁ : ∀ a b, band a b = true → a = true
  | true, _, _ => rfl

theorem and_true₂ : ∀ a b, band a b = true → b = true
  | true, _, e => e

/-! L-1: the order is a partial order -/

def le_refl (l : Label) : Le l l := ⟨ge_refl _, ge_refl _, ge_refl _⟩

def le_trans {l₁ l₂ l₃ : Label} (f : Le l₁ l₂) (g : Le l₂ l₃) : Le l₁ l₃ :=
  ⟨ge_trans f.atClient g.atClient, ge_trans f.atProxy g.atProxy, ge_trans f.atTarget g.atTarget⟩

theorem le_antisym : ∀ {l l' : Label}, Le l l' → Le l' l → l = l'
  | ⟨c, p, t⟩, ⟨c', p', t'⟩, f, g => by
    have hc : c = c' := ge_antisym f.atClient g.atClient
    have hp : p = p' := ge_antisym f.atProxy g.atProxy
    have ht : t = t' := ge_antisym f.atTarget g.atTarget
    subst hc; subst hp; subst ht; rfl

/-! L-2: the bit encoding is reverse inclusion of reader sets -/

theorem ge_sound : ∀ {a b}, Ge a b → b = true → a = true
  | _, _, .tru, _ => rfl
  | _, _, .fls, h => nomatch h

def ge_complete : ∀ a b, (b = true → a = true) → Ge a b
  | true, _, _ => .tru
  | false, false, _ => .fls
  | false, true, h => nomatch h rfl

theorem le_readers {l l' : Label} (f : Le l l') :
    ∀ r, reads l' r = true → reads l r = true
  | .client => ge_sound f.atClient
  | .proxy => ge_sound f.atProxy
  | .target => ge_sound f.atTarget

def readers_le (l l' : Label) (h : ∀ r, reads l' r = true → reads l r = true) : Le l l' :=
  ⟨ge_complete _ _ (h .client), ge_complete _ _ (h .proxy), ge_complete _ _ (h .target)⟩

/-! L-1 and L-3: joins, meets, bounds -/

def upper₁ (l l' : Label) : Le l (join l l') :=
  ⟨and_left _ _, and_left _ _, and_left _ _⟩

def upper₂ (l l' : Label) : Le l' (join l l') :=
  ⟨and_right _ _, and_right _ _, and_right _ _⟩

def join_least {l₁ l₂ l : Label} (f : Le l₁ l) (g : Le l₂ l) : Le (join l₁ l₂) l :=
  ⟨and_greatest f.atClient g.atClient, and_greatest f.atProxy g.atProxy,
   and_greatest f.atTarget g.atTarget⟩

def meet_lower₁ (l l' : Label) : Le (meet l l') l :=
  ⟨or_left _ _, or_left _ _, or_left _ _⟩

def meet_lower₂ (l l' : Label) : Le (meet l l') l' :=
  ⟨or_right _ _, or_right _ _, or_right _ _⟩

def meet_greatest {l l₁ l₂ : Label} (f : Le l l₁) (g : Le l l₂) : Le l (meet l₁ l₂) :=
  ⟨or_least f.atClient g.atClient, or_least f.atProxy g.atProxy, or_least f.atTarget g.atTarget⟩

def anyone_least (l : Label) : Le anyone l := ⟨.tru, .tru, .tru⟩

def noOne_greatest (l : Label) : Le l noOne := ⟨ge_closed _, ge_closed _, ge_closed _⟩

/-- `no-one-⋢-anyone`: the top never flows down. -/
theorem noOne_not_le_anyone : Le noOne anyone → False :=
  fun f => nomatch (f.atClient : Ge false true)

/-! L-3, the earlier two-point reading -/

theorem anyone_join : ∀ l, join anyone l = l
  | ⟨_, _, _⟩ => rfl

theorem noOne_join (l : Label) : join noOne l = noOne := rfl

theorem join_anyone₁ : ∀ {l l' : Label}, join l l' = anyone → l = anyone
  | ⟨c, p, t⟩, l', e => by
    have hc := and_true₁ c l'.byClient (congrArg Label.byClient e)
    have hp := and_true₁ p l'.byProxy (congrArg Label.byProxy e)
    have ht := and_true₁ t l'.byTarget (congrArg Label.byTarget e)
    subst hc; subst hp; subst ht; rfl

theorem join_anyone₂ : ∀ {l l' : Label}, join l l' = anyone → l' = anyone
  | l, ⟨c, p, t⟩, e => by
    have hc := and_true₂ l.byClient c (congrArg Label.byClient e)
    have hp := and_true₂ l.byProxy p (congrArg Label.byProxy e)
    have ht := and_true₂ l.byTarget t (congrArg Label.byTarget e)
    subst hc; subst hp; subst ht; rfl

/-! L-1: decidable flow.  `Dec` of `SecretTypes.Prelude` is `Type`-valued
(`yes` carries the proof), so it is restated here; Lean's `Decidable` is for
propositions only. -/

inductive Dec (A : Type) : Type where
  | yes : A → Dec A
  | no : (A → False) → Dec A

def geDec : ∀ a b, Dec (Ge a b)
  | true, _ => .yes .tru
  | false, false => .yes .fls
  | false, true => .no (fun h => nomatch h)

def leDec (l l' : Label) : Dec (Le l l') :=
  match geDec l.byClient l'.byClient, geDec l.byProxy l'.byProxy,
        geDec l.byTarget l'.byTarget with
  | .yes c, .yes p, .yes t => .yes ⟨c, p, t⟩
  | .no nc, _, _ => .no (fun f => nc f.atClient)
  | .yes _, .no np, _ => .no (fun f => np f.atProxy)
  | .yes _, .yes _, .no nt => .no (fun f => nt f.atTarget)

/-! L-2: observers -/

def observer : Role → Label
  | .client => ⟨true, false, false⟩
  | .proxy => ⟨false, true, false⟩
  | .target => ⟨false, false, true⟩

def observes_flow : ∀ (l : Label) (r : Role), reads l r = true → Le l (observer r)
  | ⟨_, p, t⟩, .client, h => by cases h; exact ⟨.tru, ge_closed p, ge_closed t⟩
  | ⟨c, _, t⟩, .proxy, h => by cases h; exact ⟨ge_closed c, .tru, ge_closed t⟩
  | ⟨c, p, _⟩, .target, h => by cases h; exact ⟨ge_closed c, ge_closed p, .tru⟩

theorem flow_observes : ∀ (l : Label) (r : Role), Le l (observer r) → reads l r = true
  | _, .client, f => ge_sound f.atClient rfl
  | _, .proxy, f => ge_sound f.atProxy rfl
  | _, .target, f => ge_sound f.atTarget rfl

/-! L-4: two fields of an oblivious query -/

def address : Label := ⟨true, true, false⟩
def qname : Label := ⟨true, false, true⟩

def address_to_proxy : Le address (observer .proxy) := ⟨.tru, .tru, .fls⟩

def qname_to_target : Le qname (observer .target) := ⟨.tru, .fls, .tru⟩

theorem link : join address qname = observer .client := rfl

def link_to_client : Le (join address qname) (observer .client) := ⟨.tru, .fls, .fls⟩

theorem link_confined : ∀ r, Le (join address qname) (observer r) → r = .client
  | .client, _ => rfl
  | .proxy, f => nomatch (f.atProxy : Ge false true)
  | .target, f => nomatch (f.atTarget : Ge false true)

end Lintel
