/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.DeferredGroundingReservedNativeRelation
import ErdosProblems.Erdos599.DeferredGroundingReservedSinkWarp
import ErdosProblems.Erdos599.GroundingClosedCarrierHindrance

/-!
# Direct deferred grounding from actual boundary reachability

The omitted grounded record has a forward-closed carrier in the native
stopped relation. The common relevant frontier is disjoint from it.
Consequently, if that frontier is rooted, the finite paths realizing it
omit this original source and already form a hindrance. This interface does
not identify selected paths from different control recursions, and does not
require a stronger stationary-family preservation output.

Rooting the common frontier remains the geometric obligation; it is not
asserted here.
-/

noncomputable section

open Cardinal Set

namespace Erdos599.DWeb.KappaLadder.Deferred

open _root_.Erdos599.DirectedPath Alternating
open GroundingErasedDecode GroundingErasedForwardConflict

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}
variable {L : Gamma.KappaLadder kappa} {hL : IsKappaHindrance L}
variable {S : Popular.PopularSeparator (popularAuxiliaryIndexed L hL)}

local notation "U" => popularAuxiliaryIndexed L hL
local notation "K" => reservedGroundedCarrierControls L hL S
local notation "R" => canonicalReservedRecord L hL S
local notation "T" =>
  reservedStrongSelectedRelevantBB (L := L) (hL := hL) (S := S)
local notation "E" =>
  reservedStrongSelectedSwitchedEdges (L := L) (hL := hL) (S := S)

/-- Every native edge leaving the reserved carrier remains in that carrier. -/
theorem reservedNative_record_forwardClosed
    {x y : V} (hxy : (x, y) ∈ E) (hx : x ∈ (R).record.support) :
    y ∈ (R).record.support :=
  ((R).record.edgeSet_subset_support_prod
    (nativeSwitch_edge_mem_reservedRecord_of_incident T hxy (Or.inl hx))).2

/-- No original-vertex native route from the reserved source can reach the
actual common relevant frontier. -/
theorem reservedNative_source_not_reaches_relevantBB
    {t : V} (ht : t ∈ T) :
    ¬ Relation.ReflTransGen (fun x y ↦ (x, y) ∈ E) (R).record.initial t := by
  intro hreach
  have htRecord := GroundingClosedCarrierHindrance.mem_of_reaches_of_closed
    (fun hxy hx ↦ reservedNative_record_forwardClosed hxy hx)
    (R).record.initial_mem_support hreach
  exact Set.disjoint_left.mp
    canonicalReservedRecord_disjoint_reservedStrongSelectedRelevantBB ht htRecord

/-- The complete finite-wave compiler once actual frontier reachability
has been established. The omitted source is the concrete reserved source. -/
theorem exists_reservedNative_hindrance_of_relevantBB_rooted
    (hroot : ∀ t ∈ T, ∃ a ∈ Gamma.source,
      Relation.ReflTransGen (fun x y ↦ (x, y) ∈ E) a t) :
    ∃ W : Set Gamma.DPath,
      Gamma.IsHindrance W ∧ Gamma.terminalFrontier W = T ∧
        (R).record.initial ∉ Gamma.initialSet W := by
  apply GroundingClosedCarrierHindrance.exists_hindrance_of_closed_source
    E T (R).record.support
    (erasedSelectedSwitchedEdgesAt_subset_adj U S K T)
    (erasedSelectedSwitchedEdgesAt_biUnique U S K T
      (popularAuxiliary_proxyPathsFaithful L hL))
    (fun _ ht ↦ boundary_noOutgoing_switchedAt U S K T ht)
    reservedStrongSelectedRelevantBB_isSeparator hroot
    (fun hxy hx ↦ reservedNative_record_forwardClosed hxy hx)
    canonicalReservedRecord_disjoint_reservedStrongSelectedRelevantBB.symm
    (R).record.initial (R).grounded (R).record.initial_mem_support

#print axioms reservedNative_record_forwardClosed
#print axioms reservedNative_source_not_reaches_relevantBB
#print axioms exists_reservedNative_hindrance_of_relevantBB_rooted

end Erdos599.DWeb.KappaLadder.Deferred
