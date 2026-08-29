/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.DeferredGroundingRawReservedRecord
import ErdosProblems.Erdos599.DeferredGroundingReservedSourceFirst
import ErdosProblems.Erdos599.GroundingClosedCarrierHindrance

/-!
# The remaining rooting obligation for the actual raw simultaneous switch

Stop the proved biunique raw relation at the genuine source-first relevant
separator. The reserved record remains closed and disjoint from that set.
Thus rooting every separator vertex in this exact stopped relation would
give the required ambient hindrance. Rooting is explicit and unproved here;
no erased relation or unrestricted reachability is substituted for it.
-/

noncomputable section

namespace Erdos599.DWeb.KappaLadder.Deferred

open Set _root_.Erdos599.DirectedPath Alternating

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}
variable {L : Gamma.KappaLadder kappa} {hL : IsKappaHindrance L}
variable {S : Popular.PopularSeparator (popularAuxiliaryIndexed L hL)}

local notation "R" => canonicalReservedRecord L hL S
local notation "E" => reservedRawSimultaneousEdges (L := L) (hL := hL) (S := S)

/-- Stop the actual simultaneous raw relation at a specified frontier. -/
def reservedRawStoppedEdges (T : Set V) : Set (V × V) :=
  {e | e ∈ E ∧ e.1 ∉ T}

theorem reservedRawStoppedEdges_biUnique (T : Set V) :
    Relator.BiUnique (fun x y ↦ (x, y) ∈
      reservedRawStoppedEdges (L := L) (hL := hL) (S := S) T) := by
  have h := reservedRawSimultaneousEdges_biUnique (L := L) (hL := hL) (S := S)
  exact ⟨fun _ _ _ h₁ h₂ ↦ h.1 h₁.1 h₂.1,
    fun _ _ _ h₁ h₂ ↦ h.2 h₁.1 h₂.1⟩

theorem reservedRawStopped_edge_iff_of_incident_reserved
    (T : Set V) (hT : Disjoint T (R).record.support) {x y : V}
    (hincident : x ∈ (R).record.support ∨ y ∈ (R).record.support) :
    (x, y) ∈ reservedRawStoppedEdges (L := L) (hL := hL) (S := S) T ↔
      (x, y) ∈ (R).record.edgeSet := by
  constructor
  · intro he
    exact (reservedRaw_edge_iff_of_incident_reserved hincident).1 he.1
  · intro he
    exact ⟨(reservedRaw_edge_iff_of_incident_reserved hincident).2 he,
      fun hxT ↦ Set.disjoint_left.1 hT hxT ((R).record.edgeSet_subset_support_prod he).1⟩

local notation "T" =>
  reservedStrongSelectedSourceFirstBB (L := L) (hL := hL) (S := S)
local notation "ES" => reservedRawStoppedEdges (L := L) (hL := hL) (S := S) T

/-- The exact remaining raw-rooting premise suffices for a genuine ambient
hindrance, omitting the actual reserved original source. -/
theorem exists_reservedRawSourceFirst_hindrance_of_rooted
    (hroot : ∀ t ∈ T, ∃ a ∈ Gamma.source,
      Relation.ReflTransGen (fun x y ↦ (x, y) ∈ ES) a t) :
    ∃ W : Set Gamma.DPath,
      Gamma.IsHindrance W ∧ Gamma.terminalFrontier W = T ∧
        (R).record.initial ∉ Gamma.initialSet W := by
  have hTdisj : Disjoint T (R).record.support :=
    Disjoint.mono reservedStrongSelectedSourceFirstBB_subset_relevantBB
      Set.Subset.rfl canonicalReservedRecord_disjoint_reservedStrongSelectedRelevantBB
  apply GroundingClosedCarrierHindrance.exists_hindrance_of_closed_source
    ES T (R).record.support
    (fun _ he ↦ reservedRawSimultaneousEdges_subset_adj he.1)
    (reservedRawStoppedEdges_biUnique T)
    (fun _ ht ⟨_y, hy⟩ ↦ hy.2 ht)
    reservedStrongSelectedSourceFirstBB_isSeparator hroot
    (fun he hx ↦ reservedRaw_record_forwardClosed he.1 hx)
    hTdisj.symm (R).record.initial (R).grounded (R).record.initial_mem_support

#print axioms reservedRawStoppedEdges_biUnique
#print axioms exists_reservedRawSourceFirst_hindrance_of_rooted

end Erdos599.DWeb.KappaLadder.Deferred
