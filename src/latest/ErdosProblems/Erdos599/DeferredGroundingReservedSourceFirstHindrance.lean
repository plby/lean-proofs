/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.DeferredGroundingReservedSourceFirst
import ErdosProblems.Erdos599.DeferredGroundingReservedNativeRelation
import ErdosProblems.Erdos599.GroundingClosedCarrierHindrance

/-!
# Deferred hindrance from source-first native reachability

The complete relevant boundary need not be rooted pointwise.  It is enough
to root its source-first separating subset.  The reserved record remains a
closed carrier for the relation stopped at this smaller frontier, and its
actual grounded source is omitted from the resulting finite wave.
-/

noncomputable section

open Cardinal Set

namespace Erdos599.DWeb.KappaLadder.Deferred

open _root_.Erdos599.DirectedPath Alternating
open GroundingErasedDecode
open GroundingErasedForwardConflict

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}
variable {L : Gamma.KappaLadder kappa} {hL : IsKappaHindrance L}
variable {S : Popular.PopularSeparator (popularAuxiliaryIndexed L hL)}

local notation "U" => popularAuxiliaryIndexed L hL
local notation "K" => reservedGroundedCarrierControls L hL S
local notation "R" => canonicalReservedRecord L hL S
local notation "T" =>
  reservedStrongSelectedSourceFirstBB (L := L) (hL := hL) (S := S)
local notation "E" => erasedSelectedSwitchedEdgesAt U S K T

/-- Every edge of the native relation stopped at the source-first frontier
which leaves the reserved carrier remains on the reserved record. -/
theorem reservedSourceFirstNative_record_forwardClosed
    {x y : V} (hxy : (x, y) ∈ E) (hx : x ∈ (R).record.support) :
    y ∈ (R).record.support := by
  have hTdisj : Disjoint T (R).record.support :=
    Disjoint.mono
      reservedStrongSelectedSourceFirstBB_subset_relevantBB
      Set.Subset.rfl
      canonicalReservedRecord_disjoint_reservedStrongSelectedRelevantBB
  exact ((R).record.edgeSet_subset_support_prod
    ((nativeSwitch_edge_iff_of_incident_reservedRecord T hTdisj
      (Or.inl hx)).mp hxy)).2

/-- Rooting only the source-first frontier in the actual final native
relation already yields an ambient hindrance. -/
theorem exists_reservedSourceFirstNative_hindrance_of_rooted
    (hroot : ∀ t ∈ T, ∃ a ∈ Gamma.source,
      Relation.ReflTransGen (fun x y ↦ (x, y) ∈ E) a t) :
    ∃ W : Set Gamma.DPath,
      Gamma.IsHindrance W ∧ Gamma.terminalFrontier W = T ∧
        (R).record.initial ∉ Gamma.initialSet W := by
  have hTdisj : Disjoint T (R).record.support :=
    Disjoint.mono
      reservedStrongSelectedSourceFirstBB_subset_relevantBB
      Set.Subset.rfl
      canonicalReservedRecord_disjoint_reservedStrongSelectedRelevantBB
  apply GroundingClosedCarrierHindrance.exists_hindrance_of_closed_source
    E T (R).record.support
    (erasedSelectedSwitchedEdgesAt_subset_adj U S K T)
    (erasedSelectedSwitchedEdgesAt_biUnique U S K T
      (popularAuxiliary_proxyPathsFaithful L hL))
    (fun _ ht ↦ boundary_noOutgoing_switchedAt U S K T ht)
    reservedStrongSelectedSourceFirstBB_isSeparator hroot
    (fun hxy hx ↦ reservedSourceFirstNative_record_forwardClosed hxy hx)
    hTdisj.symm
    (R).record.initial (R).grounded (R).record.initial_mem_support

#print axioms reservedSourceFirstNative_record_forwardClosed
#print axioms exists_reservedSourceFirstNative_hindrance_of_rooted

end Erdos599.DWeb.KappaLadder.Deferred
