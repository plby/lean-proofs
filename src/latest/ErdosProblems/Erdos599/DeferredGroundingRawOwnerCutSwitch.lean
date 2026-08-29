/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.LambdaRawOwnerCutSwitch
import ErdosProblems.Erdos599.DeferredGroundingRawOwnerAttachment
import ErdosProblems.Erdos599.DeferredGroundingRawBoundary
import ErdosProblems.Erdos599.GroundingRawSelectedEdgeSwitch

/-!
# The actual deferred selected owner transaction at a cut edge

Every attachment, source record, cut, and auxiliary path below comes from
the final reserved strong selector. The genuine record initial replaces
the ordinary/proxy starting tag in the exact balance. This is a local
path/ray transaction; simultaneous separator grounding is not asserted.
-/

noncomputable section

namespace Erdos599.DWeb.KappaLadder.Deferred

open Set _root_.Erdos599.DirectedPath Alternating Alternating.TerminalContactSwitch
open PopularAuxiliary.Input PopularGroundingBridge GroundingSimultaneousDecode
open GroundingRawSelectedEdgeSwitch

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}
variable {L : Gamma.KappaLadder kappa} {hL : IsKappaHindrance L}
variable {S : Popular.PopularSeparator (popularAuxiliaryIndexed L hL)}

local notation "J" => popularAuxiliaryInput L hL.legal
local notation "U" => popularAuxiliaryIndexed L hL
local notation "K" => reservedGroundedCarrierControls L hL S

/-- A chosen actual attachment supplied by the proved last-owner construction. -/
def reservedRawOwnerAttachment (r : Request J S.cut) :
    (J).RawOwnerAttachment (reservedStrongSelectedStartingRecord r).record
      (strongSelectedPath U S K r) :=
  Classical.choice (exists_reservedStrongSelectedRawOwnerAttachment r)

/-- The genuine source prefix is grounded and avoids the entire relevant boundary. -/
theorem reservedRawOwnerAttachment_prefix_grounded_and_avoids
    (r : Request J S.cut) :
    (reservedRawOwnerAttachment r).sourcePrefix.start ∈ Gamma.source ∧
    Disjoint (reservedStrongSelectedRelevantBB (L := L) (hL := hL) (S := S))
      (reservedRawOwnerAttachment r).sourcePrefix.support :=
  ⟨reservedStrongSelectedRawOwnerAttachment_prefix_source r (reservedRawOwnerAttachment r),
    reservedStrongSelectedRawOwnerAttachment_prefix_disjoint_relevantBB r
      (reservedRawOwnerAttachment r)⟩

/-- The explicit cut-head relation, with the actual starting record replaced. -/
def reservedRawOwnerEntryEdges (e : edgeRequests J S.cut) : Set (V × V) :=
  (reservedRawOwnerAttachment (.inr e)).entrySourceEdges e.1.1 e.1.2
    (strongSelectedPath_finish U S K (.inr e)) (GroundingCut.CE J S.cut)

/-- All degree and cut premises are discharged for the actual selected request.
No ordinary-source hypothesis is needed. -/
theorem reservedRawOwnerEntryEdges_biUnique_and_balance
    (e : edgeRequests J S.cut) :
    Relator.BiUnique (fun x y ↦ (x, y) ∈ reservedRawOwnerEntryEdges e) ∧
    ∀ x, edgeBalance (reservedRawOwnerEntryEdges e) x =
      edgeBalance (((J).familyEdges \
        (reservedStrongSelectedStartingRecord (.inr e)).record.edgeSet) \
          GroundingCut.CE J S.cut) x +
        propInt (x = (reservedStrongSelectedStartingRecord (.inr e)).record.initial) -
          propInt (x = e.1.2) := by
  let A := reservedRawOwnerAttachment (.inr e)
  have hboundary := popularAuxiliary_hasBoundaryIncidence L hL.legal
  have howner := (reservedStrongSelectedStartingRecord (.inr e)).record_mem_ladder
  have hs : (strongSelectedPath U S K (.inr e)).start ∈ (J).lambda.source :=
    (strongSelectedWarp U S K).starts_in_source ⟨.inr e, rfl⟩
  exact ⟨A.entrySourceEdges_biUnique hboundary howner hs e.1.1 e.1.2
      (strongSelectedPath_finish U S K (.inr e)) (GroundingCut.CE J S.cut)
      (selectedEdge_mem_CE U S K e),
    A.entrySourceEdges_balance hboundary howner hs e.1.1 e.1.2
      (strongSelectedPath_finish U S K (.inr e)) (GroundingCut.CE J S.cut)
      (selectedEdge_mem_CE U S K e) (selected_edgeCut_gadget_unique U S K e)⟩

/-- The actual proxy-or-finite request has a path/ray realization, with
all cut accounting and the genuine source boundary proved. -/
theorem exists_reservedRawOwnerEntrySwitchWarp (e : edgeRequests J S.cut) :
    ∃ W : Set Gamma.DPath,
      Gamma.IsWarp W ∧
      familyEdges W = reservedRawOwnerEntryEdges e \ cyclicEdges (reservedRawOwnerEntryEdges e) ∧
      isolatedVertices W = ∅ ∧
      (reservedStrongSelectedStartingRecord (.inr e)).record.initial ∈ Gamma.source ∧
      ∀ x, edgeBalance (familyEdges W) x =
        edgeBalance (((J).familyEdges \
          (reservedStrongSelectedStartingRecord (.inr e)).record.edgeSet) \
            GroundingCut.CE J S.cut) x +
          propInt (x = (reservedStrongSelectedStartingRecord (.inr e)).record.initial) -
            propInt (x = e.1.2) := by
  let A := reservedRawOwnerAttachment (.inr e)
  have hs : (strongSelectedPath U S K (.inr e)).start ∈ (J).lambda.source :=
    (strongSelectedWarp U S K).starts_in_source ⟨.inr e, rfl⟩
  obtain ⟨W, hW, hWE, hWI, hbalance⟩ := A.exists_entrySourceSwitchWarp
    (popularAuxiliary_hasBoundaryIncidence L hL.legal)
    (reservedStrongSelectedStartingRecord (.inr e)).record_mem_ladder
    hs e.1.1 e.1.2 (strongSelectedPath_finish U S K (.inr e))
    (GroundingCut.CE J S.cut) (selectedEdge_mem_CE U S K e)
    (selected_edgeCut_gadget_unique U S K e)
  exact ⟨W, hW, hWE, hWI, reservedStrongSelectedStartingRecord_grounded (.inr e), hbalance⟩

#print axioms reservedRawOwnerAttachment_prefix_grounded_and_avoids
#print axioms reservedRawOwnerEntryEdges_biUnique_and_balance
#print axioms exists_reservedRawOwnerEntrySwitchWarp

end Erdos599.DWeb.KappaLadder.Deferred
