/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingCutFreeExposure
import ErdosProblems.Erdos599.LambdaRawOwnerProvenance
import ErdosProblems.Erdos599.DeferredGroundingRawOwnerRequests
import ErdosProblems.Erdos599.DeferredGroundingSeparatorGeometry

/-!
# Source-owner separation for the actual deferred raw transactions

The selected starting records have cut-free traces, so each is exposed
by exactly its own request. Consequently restoring their genuine source
prefixes does not meet any other request's raw signed route.
-/

noncomputable section

namespace Erdos599.DWeb.KappaLadder.Deferred

open Set _root_.Erdos599.DirectedPath
open PopularAuxiliary.Input PopularGroundingBridge GroundingSimultaneousDecode
open GroundingCutFreeExposure

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}
variable {L : Gamma.KappaLadder kappa} {hL : IsKappaHindrance L}
variable {S : Popular.PopularSeparator (popularAuxiliaryIndexed L hL)}

local notation "J" => popularAuxiliaryInput L hL.legal
local notation "U" => popularAuxiliaryIndexed L hL
local notation "K" => reservedGroundedCarrierControls L hL S

theorem reservedRawOwner_record_exposed (r : Request J S.cut) :
    (reservedStrongSelectedStartingRecord r).record ∈
      exposedLadderPaths J (strongSelectedPath U S K r) :=
  represented_mem_exposed (reservedStrongSelectedStartingRecord r).record_mem_ladder
    _ (reservedStrongSelectedStartingRecord r).represents

theorem reservedRawOwner_record_not_exposed_other
    (r s : Request J S.cut) (hrs : r ≠ s) :
    (reservedStrongSelectedStartingRecord r).record ∉
      exposedLadderPaths J (strongSelectedPath U S K s) := by
  intro hs
  apply hrs
  exact exposed_request_unique_of_cutFree U S K (popularAuxiliary_proxyPathsFaithful L hL)
    ((reservedStrongSelectedStartingRecord_ownCarrier_disjoint_cut r).mono_left
      Set.subset_union_left) r s (reservedRawOwner_record_exposed r) hs

/-- The whole starting owner, not just the restored prefix, avoids all
original vertices decoded from another actual selected path. -/
theorem reservedRawOwner_record_disjoint_other_carrier
    (r s : Request J S.cut) (hrs : r ≠ s) :
    Disjoint (reservedStrongSelectedStartingRecord r).record.support
      ((J).decodedVertexCarrier (strongSelectedPath U S K s)) :=
  represented_owner_disjoint_other_carrier U S K (popularAuxiliary_proxyPathsFaithful L hL)
    (reservedStrongSelectedStartingRecord r).record_mem_ladder
    ((reservedStrongSelectedStartingRecord_ownCarrier_disjoint_cut r).mono_left
      Set.subset_union_left) r s hrs (reservedStrongSelectedStartingRecord r).represents

theorem reservedRawOwner_record_ne (r s : Request J S.cut) (hrs : r ≠ s) :
    (reservedStrongSelectedStartingRecord r).record ≠
      (reservedStrongSelectedStartingRecord s).record := by
  intro hrecords
  exact reservedRawOwner_record_not_exposed_other r s hrs
    (hrecords.symm ▸ reservedRawOwner_record_exposed s)

/-- The genuine restored prefixes of all actual requests are pairwise disjoint. -/
theorem reservedRawOwner_prefixes_pairwiseDisjoint :
    Set.PairwiseDisjoint Set.univ
      (fun r : Request J S.cut ↦ (reservedRawOwnerAttachment r).sourcePrefix.support) := by
  intro r _hr s _hs hrs
  exact ((J).ladder.disjoint
    (reservedStrongSelectedStartingRecord r).record_mem_ladder
    (reservedStrongSelectedStartingRecord s).record_mem_ladder
    (reservedRawOwner_record_ne r s hrs)).mono
      (reservedRawOwnerAttachment r).sourcePrefix_support
      (reservedRawOwnerAttachment s).sourcePrefix_support

/-- Every inserted forward edge of another request avoids the whole starting owner. -/
theorem reservedRawOwner_forward_other_avoids_record
    (r s : Request J S.cut) (hrs : r ≠ s) {e : V × V}
    (he : e ∈ (reservedRawOwnerAttachment s).forwardEdges) :
    e.1 ∉ (reservedStrongSelectedStartingRecord r).record.support ∧
      e.2 ∉ (reservedStrongSelectedStartingRecord r).record.support := by
  have hends := (reservedRawOwnerAttachment s).forwardEdges_endpoints_mem_originalCarrier he
  have hdisj := reservedRawOwner_record_disjoint_other_carrier r s hrs
  exact ⟨fun hx ↦ Set.disjoint_left.1 hdisj hx hends.1,
    fun hy ↦ Set.disjoint_left.1 hdisj hy hends.2⟩

#print axioms reservedRawOwner_record_disjoint_other_carrier
#print axioms reservedRawOwner_prefixes_pairwiseDisjoint
#print axioms reservedRawOwner_forward_other_avoids_record

end Erdos599.DWeb.KappaLadder.Deferred
