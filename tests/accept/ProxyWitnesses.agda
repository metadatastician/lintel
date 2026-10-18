{-# OPTIONS --safe --without-K #-}
-- SPDX-License-Identifier: MPL-2.0
module ProxyWitnesses where
open import Lintel.Lattice

-- The rejection in LinkToProxy must have just one bad witness. Check its
-- other two arguments independently, so a bad target witness cannot mask
-- whether the proxy flow was rejected for the intended reason.
client-witness : by-client (address ⊔ qname) ⊒ by-client (observer proxy)
client-witness = ⊒-true

target-witness : by-target (address ⊔ qname) ⊒ by-target (observer proxy)
target-witness = ⊒-false

-- With the query name removed, the proxy may observe the address. The same
-- constructor arguments used by LinkToProxy must succeed in this control.
address-only : address ⊑ observer proxy
address-only = flows ⊒-true ⊒-true ⊒-false
