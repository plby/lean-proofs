/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.DeferredGroundingRawOwnerCutSwitch
import ErdosProblems.Erdos599.LambdaRawOwnerOldCutSwitch

/-!
# A genuine-source local transaction for every deferred request

The old-vertex branch retains the whole attached signed word; the edge
branch omits its final backward gadget. Both use the actual selector, cut,
starting record and genuine source prefix, with no extra cut or ordinary
source assumptions. The resulting local warps are not yet combined.
-/

noncomputable section

namespace Erdos599.DWeb.KappaLadder.Deferred

open Set _root_.Erdos599.DirectedPath Alternating Alternating.TerminalContactSwitch
open PopularAuxiliary.Input PopularGroundingBridge GroundingSimultaneousDecode

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}
variable {L : Gamma.KappaLadder kappa} {hL : IsKappaHindrance L}
variable {S : Popular.PopularSeparator (popularAuxiliaryIndexed L hL)}

local notation "J" => popularAuxiliaryInput L hL.legal
local notation "U" => popularAuxiliaryIndexed L hL
local notation "K" => reservedGroundedCarrierControls L hL S

/-- The actual old request meets no edge gadget from the auxiliary cut. -/
theorem reservedRawOwnerOldRequest_no_cut_gadget (z : oldRequests J S.cut)
    (e : V × V) (he : e ∈ GroundingCut.CE J S.cut) :
    LambdaVertex.edge e.1 e.2 ∉ (strongSelectedPath U S K (.inl z)).support := by
  intro hmem
  have h := strongSelectedPath_cut_contact_eq_requestAuxVertex U S K (.inl z) hmem he.1
  cases h

/-- Exact local relation for either request kind, stopping at its original vertex. -/
def reservedRawOwnerRequestEdges : Request J S.cut → Set (V × V)
  | .inl z => (reservedRawOwnerAttachment (.inl z)).cutSourceEdges (GroundingCut.CE J S.cut)
  | .inr e => reservedRawOwnerEntryEdges e

/-- The actual selected local transactions all have the correct genuine-source balance. -/
theorem reservedRawOwnerRequestEdges_biUnique_and_balance (r : Request J S.cut) :
    Relator.BiUnique (fun x y ↦ (x, y) ∈ reservedRawOwnerRequestEdges r) ∧
    ∀ x, edgeBalance (reservedRawOwnerRequestEdges r) x =
      edgeBalance (((J).familyEdges \ (reservedStrongSelectedStartingRecord r).record.edgeSet) \
        GroundingCut.CE J S.cut) x +
      propInt (x = (reservedStrongSelectedStartingRecord r).record.initial) -
        propInt (x = requestVertex r) := by
  cases r with
  | inl z =>
      let A := reservedRawOwnerAttachment (.inl z)
      have hboundary := popularAuxiliary_hasBoundaryIncidence L hL.legal
      have howner := (reservedStrongSelectedStartingRecord (.inl z)).record_mem_ladder
      have hs : (strongSelectedPath U S K (.inl z)).start ∈ (J).lambda.source :=
        (strongSelectedWarp U S K).starts_in_source ⟨.inl z, rfl⟩
      have hexit : (J).gadgetExit (strongSelectedPath U S K (.inl z)).finish = some z.1 := by
        rw [strongSelectedPath_finish]
        rfl
      exact ⟨A.cutSourceEdges_biUnique hboundary howner (GroundingCut.CE J S.cut),
        A.cutSourceEdges_balance hboundary howner hs hexit (GroundingCut.CE J S.cut)
          (reservedRawOwnerOldRequest_no_cut_gadget z)⟩
  | inr e => exact reservedRawOwnerEntryEdges_biUnique_and_balance e

/-- Both final selector branches produce an actual cycle-discarded path/ray
warp. Its replacement owner is grounded; no simultaneous grounding is assumed. -/
theorem exists_reservedRawOwnerRequestSwitchWarp (r : Request J S.cut) :
    ∃ W : Set Gamma.DPath,
      Gamma.IsWarp W ∧
      familyEdges W = reservedRawOwnerRequestEdges r \
        cyclicEdges (reservedRawOwnerRequestEdges r) ∧
      isolatedVertices W = ∅ ∧
      (reservedStrongSelectedStartingRecord r).record.initial ∈ Gamma.source ∧
      ∀ x, edgeBalance (familyEdges W) x =
        edgeBalance (((J).familyEdges \ (reservedStrongSelectedStartingRecord r).record.edgeSet) \
          GroundingCut.CE J S.cut) x +
        propInt (x = (reservedStrongSelectedStartingRecord r).record.initial) -
          propInt (x = requestVertex r) := by
  cases r with
  | inl z =>
      let A := reservedRawOwnerAttachment (.inl z)
      have hs : (strongSelectedPath U S K (.inl z)).start ∈ (J).lambda.source :=
        (strongSelectedWarp U S K).starts_in_source ⟨.inl z, rfl⟩
      have hexit : (J).gadgetExit (strongSelectedPath U S K (.inl z)).finish = some z.1 := by
        rw [strongSelectedPath_finish]
        rfl
      obtain ⟨W, hW, hWE, hWI, hbalance⟩ := A.exists_cutSourceSwitchWarp
        (popularAuxiliary_hasBoundaryIncidence L hL.legal)
        (reservedStrongSelectedStartingRecord (.inl z)).record_mem_ladder
        hs hexit (GroundingCut.CE J S.cut) (reservedRawOwnerOldRequest_no_cut_gadget z)
      exact ⟨W, hW, hWE, hWI, reservedStrongSelectedStartingRecord_grounded (.inl z), hbalance⟩
  | inr e => exact exists_reservedRawOwnerEntrySwitchWarp e

#print axioms reservedRawOwnerRequestEdges_biUnique_and_balance
#print axioms exists_reservedRawOwnerRequestSwitchWarp

end Erdos599.DWeb.KappaLadder.Deferred
