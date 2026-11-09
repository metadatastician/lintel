-- SPDX-License-Identifier: MPL-2.0
-- Prints the axioms every Lean-leg theorem rests on (PROOF-POLICY §8.4).
-- scripts/check-legs.sh requires each line to read "does not depend on any axioms".
import Lintel
-- L-1
#print axioms Lintel.le_refl
#print axioms Lintel.le_trans
#print axioms Lintel.le_antisym
#print axioms Lintel.upper₁
#print axioms Lintel.upper₂
#print axioms Lintel.join_least
#print axioms Lintel.meet_lower₁
#print axioms Lintel.meet_lower₂
#print axioms Lintel.meet_greatest
#print axioms Lintel.anyone_least
#print axioms Lintel.noOne_greatest
#print axioms Lintel.noOne_not_le_anyone
#print axioms Lintel.leDec
-- L-2
#print axioms Lintel.le_readers
#print axioms Lintel.readers_le
#print axioms Lintel.observes_flow
#print axioms Lintel.flow_observes
-- L-3
#print axioms Lintel.readerSets
#print axioms Lintel.anyone_join
#print axioms Lintel.noOne_join
#print axioms Lintel.join_anyone₁
#print axioms Lintel.join_anyone₂
-- L-4
#print axioms Lintel.address_to_proxy
#print axioms Lintel.qname_to_target
#print axioms Lintel.link
#print axioms Lintel.link_confined
-- L-6
#print axioms Lintel.tini_per_role
#print axioms Lintel.tini_coalition
-- A-1, the proved half
#print axioms Lintel.collusion_gap
#print axioms Lintel.coalition_blind
#print axioms Lintel.coalition_agrees
#print axioms Lintel.stores_differ
-- L-7
#print axioms Lintel.writes_flow
#print axioms Lintel.link_written_to_client
#print axioms Lintel.link_written_to_local
#print axioms Lintel.link_writable
