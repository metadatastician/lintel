(* SPDX-License-Identifier: MPL-2.0
   SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

   Rocq leg (PROOF-POLICY §2, route `re-proved`) of Lintel L-1, L-2, L-3,
   L-4, L-6, L-7 and the proved half of A-1.  Mirrors src/Lintel/Lattice.agda,
   Instance.agda and Composition.agda, statement by statement.

   The record, the language, the typing rules and TINI are secret-types',
   loaded from its own Rocq leg at the pin (scripts/fetch-siblings.sh), as
   the Agda modules import them from secret-types' Agda sources.  That one
   `Require` is the only one: no standard library, only Coq's prelude.  No
   axioms: the `Print Assumptions` commands at the end must report
   "Closed under the global context".

   Universe discipline: Agda's `Set` is `Type`.  The bit order, the label
   order, observers' `sees` and the `Writes` relation are `Type`-valued, as
   in Agda.  Equalities are `Prop`, of booleans, labels, roles and fields,
   all decidable, so the two readings hold the same information. *)

Require SecretTypesLeg.SecretTypes.
Module ST := SecretTypesLeg.SecretTypes.
(* Only the coercion from a lattice to its signature, as secret-types uses it. *)
Import (coercions) SecretTypesLeg.SecretTypes.

(* ---------------------------------------------------------------------- *)
(* Lintel.Lattice: roles and labels                                        *)

Inductive Role := client | proxy | target.

Record Label := mkLabel { byClient : bool; byProxy : bool; byTarget : bool }.

Definition reads (l : Label) (r : Role) : bool :=
  match r with client => byClient l | proxy => byProxy l | target => byTarget l end.

Definition anyone : Label := mkLabel true true true.
Definition no_one : Label := mkLabel false false false.

(* a ⊒ b: every reader b admits, a admits too. *)
Inductive Ge : bool -> bool -> Type :=
| ge_true : forall b, Ge true b
| ge_false : Ge false false.

(* ℓ ⊑ ℓ', the record _⊑_ with constructor flows. *)
Record Le (l l' : Label) : Type := flows {
  at_client : Ge (byClient l) (byClient l');
  at_proxy : Ge (byProxy l) (byProxy l');
  at_target : Ge (byTarget l) (byTarget l')
}.
Arguments flows {l l'} & _ _ _.
Arguments at_client {l l'} _.
Arguments at_proxy {l l'} _.
Arguments at_target {l l'} _.

(* _∧_ and _∨_ of Lintel.Lattice, by the same clauses. *)
Definition band (a b : bool) : bool := match a with true => b | false => false end.
Definition bor (a b : bool) : bool := match a with true => true | false => b end.

Definition join (l l' : Label) : Label :=
  mkLabel (band (byClient l) (byClient l')) (band (byProxy l) (byProxy l'))
          (band (byTarget l) (byTarget l')).
Definition meet (l l' : Label) : Label :=
  mkLabel (bor (byClient l) (byClient l')) (bor (byProxy l) (byProxy l'))
          (bor (byTarget l) (byTarget l')).

(* ---------------------------------------------------------------------- *)
(* Bit lemmas                                                              *)

Definition ge_refl (b : bool) : Ge b b :=
  match b with true => ge_true true | false => ge_false end.

Definition ge_trans {a b c} (p : Ge a b) : Ge b c -> Ge a c :=
  match p in Ge a b return Ge b c -> Ge a c with
  | ge_true _ => fun _ => ge_true c
  | ge_false => fun q => q
  end.

Definition ge_open {a} (p : Ge a true) : a = true :=
  match p in Ge a b return b = true -> a = true with
  | ge_true _ => fun _ => eq_refl
  | ge_false => fun e => e
  end eq_refl.

Definition ge_antisym {a b} (p : Ge a b) : Ge b a -> a = b :=
  match p in Ge a b return Ge b a -> a = b with
  | ge_true b => fun q => eq_sym (ge_open q)
  | ge_false => fun _ => eq_refl
  end.

Definition ge_closed (b : bool) : Ge b false :=
  match b with true => ge_true false | false => ge_false end.

Definition and_left (a b : bool) : Ge a (band a b) :=
  match a with true => ge_true b | false => ge_false end.

Definition and_right (a b : bool) : Ge b (band a b) :=
  match a with true => ge_refl b | false => ge_closed b end.

Definition and_greatest {a b c} (p : Ge a c) : Ge b c -> Ge (band a b) c :=
  match p in Ge a c return Ge b c -> Ge (band a b) c with
  | ge_true _ => fun q => q
  | ge_false => fun _ => ge_false
  end.

Definition or_left (a b : bool) : Ge (bor a b) a :=
  match a with true => ge_true true | false => ge_closed b end.

Definition or_right (a b : bool) : Ge (bor a b) b :=
  match a with true => ge_true b | false => ge_refl b end.

Definition or_least {a b c} (p : Ge c a) : Ge c b -> Ge c (bor a b) :=
  match p in Ge c a return Ge c b -> Ge c (bor a b) with
  | ge_true _ => fun _ => ge_true _
  | ge_false => fun q => q
  end.

Definition and_true1 (a b : bool) : band a b = true -> a = true :=
  match a return band a b = true -> a = true with
  | true => fun _ => eq_refl
  | false => fun e => e
  end.

Definition and_true2 (a b : bool) : band a b = true -> b = true :=
  match a return band a b = true -> b = true with
  | true => fun e => e
  | false => fun e => match e in _ = y return (if y then b = true else True) with
                      | eq_refl => I end
  end.

(* ---------------------------------------------------------------------- *)
(* L-1: the order is a partial order                                       *)

Definition le_refl (l : Label) : Le l l :=
  flows (ge_refl _) (ge_refl _) (ge_refl _).

Definition le_trans {l1 l2 l3} (f : Le l1 l2) (g : Le l2 l3) : Le l1 l3 :=
  flows (ge_trans (at_client f) (at_client g)) (ge_trans (at_proxy f) (at_proxy g))
        (ge_trans (at_target f) (at_target g)).

Lemma le_antisym : forall l l', Le l l' -> Le l' l -> l = l'.
Proof.
  intros [c p t] [c' p' t'] f g.
  pose proof (ge_antisym (at_client f) (at_client g)) as hc.
  pose proof (ge_antisym (at_proxy f) (at_proxy g)) as hp.
  pose proof (ge_antisym (at_target f) (at_target g)) as ht.
  simpl in hc, hp, ht. subst c' p' t'. reflexivity.
Qed.

(* ---------------------------------------------------------------------- *)
(* L-2: reverse inclusion of reader sets                                   *)

Definition ge_sound {a b} (p : Ge a b) : b = true -> a = true :=
  match p in Ge a b return b = true -> a = true with
  | ge_true _ => fun _ => eq_refl
  | ge_false => fun e => e
  end.

Definition ge_complete (a b : bool) : (b = true -> a = true) -> Ge a b :=
  match a, b return (b = true -> a = true) -> Ge a b with
  | true, b => fun _ => ge_true b
  | false, false => fun _ => ge_false
  | false, true => fun h => match h eq_refl in _ = y
                                  return (if y then Ge false true else True) with
                            | eq_refl => I end
  end.

Definition le_readers {l l'} (f : Le l l') (r : Role) :
  reads l' r = true -> reads l r = true :=
  match r with
  | client => ge_sound (at_client f)
  | proxy => ge_sound (at_proxy f)
  | target => ge_sound (at_target f)
  end.

Definition readers_le (l l' : Label) (h : forall r, reads l' r = true -> reads l r = true)
  : Le l l' :=
  flows (ge_complete _ _ (h client)) (ge_complete _ _ (h proxy)) (ge_complete _ _ (h target)).

(* ---------------------------------------------------------------------- *)
(* L-1 and L-3: joins, meets, bounds                                       *)

Definition upper1 (l l' : Label) : Le l (join l l') :=
  flows (and_left _ _) (and_left _ _) (and_left _ _).
Definition upper2 (l l' : Label) : Le l' (join l l') :=
  flows (and_right _ _) (and_right _ _) (and_right _ _).
Definition join_least {l1 l2 l} (f : Le l1 l) (g : Le l2 l) : Le (join l1 l2) l :=
  flows (and_greatest (at_client f) (at_client g)) (and_greatest (at_proxy f) (at_proxy g))
        (and_greatest (at_target f) (at_target g)).
Definition meet_lower1 (l l' : Label) : Le (meet l l') l :=
  flows (or_left _ _) (or_left _ _) (or_left _ _).
Definition meet_lower2 (l l' : Label) : Le (meet l l') l' :=
  flows (or_right _ _) (or_right _ _) (or_right _ _).
Definition meet_greatest {l l1 l2} (f : Le l l1) (g : Le l l2) : Le l (meet l1 l2) :=
  flows (or_least (at_client f) (at_client g)) (or_least (at_proxy f) (at_proxy g))
        (or_least (at_target f) (at_target g)).
Definition anyone_least (l : Label) : Le anyone l :=
  flows (ge_true _) (ge_true _) (ge_true _).
Definition no_one_greatest (l : Label) : Le l no_one :=
  flows (ge_closed _) (ge_closed _) (ge_closed _).

(* A bit that admits an open bit cannot be closed. *)
Definition ge_false_true (p : Ge false true) : False :=
  match p in Ge a b return (if a then True else if b then False else True) with
  | ge_true _ => I
  | ge_false => I
  end.

(* no-one-⋢-anyone: the top never flows down. *)
Definition no_one_not_le_anyone (f : Le no_one anyone) : False :=
  ge_false_true (at_client f).

(* The earlier two-point reading. *)
Lemma anyone_join : forall l, join anyone l = l.
Proof. intros [c p t]. reflexivity. Qed.

Lemma no_one_join : forall l, join no_one l = no_one.
Proof. reflexivity. Qed.

Lemma join_anyone1 : forall l l', join l l' = anyone -> l = anyone.
Proof.
  intros [c p t] l' e.
  pose proof (and_true1 c (byClient l') (f_equal byClient e)) as hc.
  pose proof (and_true1 p (byProxy l') (f_equal byProxy e)) as hp.
  pose proof (and_true1 t (byTarget l') (f_equal byTarget e)) as ht.
  subst c p t. reflexivity.
Qed.

Lemma join_anyone2 : forall l l', join l l' = anyone -> l' = anyone.
Proof.
  intros l [c p t] e.
  pose proof (and_true2 (byClient l) c (f_equal byClient e)) as hc.
  pose proof (and_true2 (byProxy l) p (f_equal byProxy e)) as hp.
  pose proof (and_true2 (byTarget l) t (f_equal byTarget e)) as ht.
  subst c p t. reflexivity.
Qed.

(* L-1: decidable flow.  Dec of SecretTypes.Prelude, Type-valued. *)
Inductive Dec (A : Type) : Type := yes : A -> Dec A | no : (A -> False) -> Dec A.
Arguments yes {A} _.
Arguments no {A} _.

Definition ge_dec (a b : bool) : Dec (Ge a b) :=
  match a, b with
  | true, b => yes (ge_true b)
  | false, false => yes ge_false
  | false, true => no ge_false_true
  end.

Definition le_dec (l l' : Label) : Dec (Le l l') :=
  match ge_dec (byClient l) (byClient l'), ge_dec (byProxy l) (byProxy l'),
        ge_dec (byTarget l) (byTarget l') with
  | yes c, yes p, yes t => yes (flows c p t)
  | no nc, _, _ => no (fun f => nc (at_client f))
  | yes _, no np, _ => no (fun f => np (at_proxy f))
  | yes _, yes _, no nt => no (fun f => nt (at_target f))
  end.

(* ---------------------------------------------------------------------- *)
(* L-2: observers                                                          *)

Definition observer (r : Role) : Label :=
  match r with
  | client => mkLabel true false false
  | proxy => mkLabel false true false
  | target => mkLabel false false true
  end.

Definition observes_flow (l : Label) (r : Role) : reads l r = true -> Le l (observer r).
Proof.
  destruct l as [c p t], r; simpl; intro h; subst.
  - exact (flows (ge_true _) (ge_closed p) (ge_closed t)).
  - exact (flows (ge_closed c) (ge_true _) (ge_closed t)).
  - exact (flows (ge_closed c) (ge_closed p) (ge_true _)).
Defined.

Definition flow_observes (l : Label) (r : Role) : Le l (observer r) -> reads l r = true :=
  match r with
  | client => fun f => ge_sound (at_client f) eq_refl
  | proxy => fun f => ge_sound (at_proxy f) eq_refl
  | target => fun f => ge_sound (at_target f) eq_refl
  end.

(* ---------------------------------------------------------------------- *)
(* L-4: two fields of an oblivious query                                   *)

Definition address : Label := mkLabel true true false.
Definition qname : Label := mkLabel true false true.

Definition address_to_proxy : Le address (observer proxy) :=
  flows (ge_true _) (ge_true _) ge_false.
Definition qname_to_target : Le qname (observer target) :=
  flows (ge_true _) ge_false (ge_true _).

Lemma link : join address qname = observer client.
Proof. reflexivity. Qed.

Definition link_to_client : Le (join address qname) (observer client) :=
  flows (ge_true _) ge_false ge_false.

Definition link_confined (r : Role) : Le (join address qname) (observer r) -> r = client :=
  match r with
  | client => fun _ => eq_refl
  | proxy => fun f => False_ind _ (ge_false_true (at_proxy f))
  | target => fun f => False_ind _ (ge_false_true (at_target f))
  end.

(* ---------------------------------------------------------------------- *)
(* Lintel.Instance: L-6.  The record is secret-types'.                    *)

Definition reader_sig : ST.Signature :=
  {| ST.Carrier := Label; ST.le := Le; ST.join := join; ST.bot := anyone |}.

Definition reader_sets : ST.Lattice :=
  {| ST.sig := reader_sig;
     ST.le_trans := fun x y z f g => le_trans f g;
     ST.upper1 := upper1;
     ST.upper2 := upper2 |}.

Inductive Field := addr | qn | local.

Definition field_deq (x y : Field) : {x = y} + {x <> y}.
Proof. destruct x, y; (left; reflexivity) || (right; discriminate). Defined.

Definition fields : ST.Vars := {| ST.Var := Field; ST.deq := field_deq |}.

Definition field_label (x : ST.Var fields) : ST.Carrier reader_sets :=
  match x with addr => address | qn => qname | local => observer client end.

Definition role (r : Role) : ST.Observer reader_sets := ST.principal reader_sets (observer r).

Theorem tini_per_role (r : Role) : ST.TINI reader_sets field_label (ST.sees (role r)).
Proof. exact (ST.tini reader_sets field_label (role r)). Qed.

(* Coalitions: a union of down-closed observers is down-closed. *)
Definition union {L : ST.Lattice} (V W : ST.Observer L) : ST.Observer L :=
  {| ST.sees := fun l => (ST.sees V l + ST.sees W l)%type;
     ST.down := fun x y p v => match v with
                               | inl a => inl (ST.down V p a)
                               | inr b => inr (ST.down W p b)
                               end |}.

Definition coalition (r r' : Role) : ST.Observer reader_sets := union (role r) (role r').

Theorem tini_coalition (r r' : Role) :
  ST.TINI reader_sets field_label (ST.sees (coalition r r')).
Proof. exact (ST.tini reader_sets field_label (coalition r r')). Qed.

(* collusion-gap: proxy and target together see each field, not their
   composition. *)
Definition collusion_gap :
  (ST.sees (coalition proxy target) address
   * (ST.sees (coalition proxy target) qname
      * (ST.sees (coalition proxy target) (join address qname) -> False)))%type :=
  (inl address_to_proxy, (inr qname_to_target,
    fun (v : ST.sees (coalition proxy target) (join address qname)) =>
     match v with
     | inl f => ge_false_true (at_proxy (l := join address qname) (l' := observer proxy) f)
     | inr f => ge_false_true (at_target (l := join address qname) (l' := observer target) f)
     end)).

Definition coalition_blind : ST.sees (coalition proxy target) (field_label local) -> False :=
  snd (snd collusion_gap).

Definition store0 : ST.Store fields := fun _ => 0.
Definition store1 : ST.Store fields :=
  fun x => match x with addr => 0 | qn => 0 | local => 1 end.

Lemma coalition_agrees :
  ST.Agree reader_sets field_label (ST.sees (coalition proxy target)) store0 store1.
Proof.
  intros [| |] v; try reflexivity.
  exact (False_ind _ (coalition_blind v)).
Qed.

Lemma stores_differ : store0 local <> store1 local.
Proof. discriminate. Qed.

(* ---------------------------------------------------------------------- *)
(* Lintel.Composition: L-7.  Commands and typing are secret-types', at the
   reader-set signature (Typing.Generic 𝓥 _⊑_ _⊔_ anyone label).          *)

Section Composition.
Context {V : ST.Vars} (label : ST.Var V -> Label).

Notation labe := (ST.lab reader_sig label).
Notation typed := (ST.Typed reader_sig label).

Inductive Writes (x : ST.Var V) : Label -> ST.Cmd V -> Type :=
| here : forall e, Writes x (labe e) (ST.assign x e)
| seq1 : forall k c1 c2, Writes x k c1 -> Writes x k (ST.seq c1 c2)
| seq2 : forall k c1 c2, Writes x k c2 -> Writes x k (ST.seq c1 c2)
| ifz1 : forall k g c1 c2, Writes x k c1 -> Writes x (join (labe g) k) (ST.ifz g c1 c2)
| ifz2 : forall k g c1 c2, Writes x k c2 -> Writes x (join (labe g) k) (ST.ifz g c1 c2)
| body : forall k g c, Writes x k c -> Writes x (join (labe g) k) (ST.while g c).

Definition under_guard {x k} (pc : Label) (g : ST.Expr V)
  (h : Le (join pc (labe g)) (label x) * Le k (label x))
  : Le pc (label x) * Le (join (labe g) k) (label x) :=
  (le_trans (upper1 pc _) (fst h), join_least (le_trans (upper2 pc _) (fst h)) (snd h)).

(* writes-flow, by induction on the Writes derivation and inversion of the
   typing derivation.  Rocq, like Lean, has the constructor injectivity the
   Agda proof avoids under --cubical-compatible (it goes through Writes′);
   the statement is the same. *)
Definition writes_flow : forall pc c x k, typed pc c -> Writes x k c ->
  (Le pc (label x) * Le k (label x))%type.
Proof.
  intros pc c x k t w. revert pc t.
  induction w as [e|k c1 c2 w IH|k c1 c2 w IH|k g c1 c2 w IH|k g c1 c2 w IH|k g c w IH];
    intros pc t; inversion t; subst.
  - match goal with ok : ST.le _ _ _ |- _ =>
      exact (le_trans (upper1 pc _) ok, le_trans (upper2 pc _) ok) end.
  - auto.
  - auto.
  - exact (under_guard pc g (IH _ X)).
  - exact (under_guard pc g (IH _ X0)).
  - exact (under_guard pc g (IH _ X)).
Defined.

Lemma link_written_to_client pc c x k (r : Role) (t : typed pc c) (w : Writes x k c)
  (h : Le (join address qname) (join pc k)) (obs : Le (label x) (observer r)) : r = client.
Proof.
  destruct (writes_flow pc c x k t w) as [p q].
  exact (link_confined r (le_trans h (le_trans (join_least p q) obs))).
Qed.

End Composition.

Lemma link_written_to_local pc c (x : Field) k :
  ST.Typed reader_sig field_label pc c -> Writes (V := fields) field_label x k c ->
  Le (join address qname) (join pc k) -> x = local.
Proof.
  intros t w h. destruct x.
  - discriminate (link_written_to_client field_label pc c addr k proxy t w h address_to_proxy).
  - discriminate (link_written_to_client field_label pc c qn k target t w h qname_to_target).
  - reflexivity.
Qed.

Definition link_expr : ST.Expr fields := ST.plus (ST.var (V := fields) addr) (ST.var (V := fields) qn).

Definition link_writable :
  { c : ST.Cmd fields & (ST.Typed reader_sig field_label anyone c
                         * Writes (V := fields) field_label local (join address qname) c)%type } :=
  existT _ (ST.assign (V := fields) local link_expr)
    (ST.t_assign (S := reader_sig) (label := field_label) (pc := anyone) (x := local) (e := link_expr)
       (flows (l := mkLabel true false false) (l' := observer client) (ge_true _) ge_false ge_false),
     here field_label local link_expr).

(* ---------------------------------------------------------------------- *)
(* Assumptions (PROOF-POLICY §8.4): each must be closed.                   *)

Print Assumptions le_refl.
Print Assumptions le_trans.
Print Assumptions le_antisym.
Print Assumptions upper1.
Print Assumptions upper2.
Print Assumptions join_least.
Print Assumptions meet_lower1.
Print Assumptions meet_lower2.
Print Assumptions meet_greatest.
Print Assumptions anyone_least.
Print Assumptions no_one_greatest.
Print Assumptions no_one_not_le_anyone.
Print Assumptions le_dec.
Print Assumptions le_readers.
Print Assumptions readers_le.
Print Assumptions observes_flow.
Print Assumptions flow_observes.
Print Assumptions reader_sets.
Print Assumptions anyone_join.
Print Assumptions no_one_join.
Print Assumptions join_anyone1.
Print Assumptions join_anyone2.
Print Assumptions address_to_proxy.
Print Assumptions qname_to_target.
Print Assumptions link.
Print Assumptions link_confined.
Print Assumptions tini_per_role.
Print Assumptions tini_coalition.
Print Assumptions collusion_gap.
Print Assumptions coalition_blind.
Print Assumptions coalition_agrees.
Print Assumptions stores_differ.
Print Assumptions writes_flow.
Print Assumptions link_written_to_client.
Print Assumptions link_written_to_local.
Print Assumptions link_writable.
