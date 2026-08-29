/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.LambdaRawOwnerAttachment
import ErdosProblems.Erdos599.DeferredGroundingReservedRelevantPruning

/-!
# Raw source attachment for the actual deferred strong selector

The real starting record is grounded and its entire trace avoids the cut.
Thus the generic last-owner construction applies to every selected request,
including those starting at a proxy. Its genuine source prefix avoids the
relevant separating boundary because the whole starting record does.
-/

noncomputable section

open Set

namespace Erdos599
namespace DWeb.KappaLadder.Deferred

open _root_.Erdos599.DirectedPath PopularAuxiliary.Input
open PopularGroundingBridge GroundingSimultaneousDecode

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}
variable {L : Gamma.KappaLadder kappa} {hL : IsKappaHindrance L}
variable {S : Popular.PopularSeparator (popularAuxiliaryIndexed L hL)}

local notation "J" => popularAuxiliaryInput L hL.legal
local notation "U" => popularAuxiliaryIndexed L hL
local notation "K" => reservedGroundedCarrierControls L hL S

/-- The actual final selected request has a genuine starting-owner prefix
and an unchanged, proxy-free raw suffix avoiding that owner. -/
theorem exists_reservedStrongSelectedRawOwnerAttachment
    (r : Request J S.cut) :
    Nonempty ((J).RawOwnerAttachment (reservedStrongSelectedStartingRecord r).record
      (strongSelectedPath U S K r)) := by
  let R := reservedStrongSelectedStartingRecord r
  let p := strongSelectedPath U S K r
  apply (J).exists_rawOwnerAttachment R.record R.record_mem_ladder p R.represents
  · intro hfinish
    apply Set.disjoint_left.1
      (reservedStrongSelectedStartingRecord_ownCarrier_disjoint_cut r)
      (Or.inl hfinish)
    rw [strongSelectedPath_finish]
    exact requestAuxVertex_mem_cut r
  · intro i
    rw [strongSelectedPath_finish]
    cases r <;> simp [requestAuxVertex]

/-- The retained prefix really starts at the original source. -/
theorem reservedStrongSelectedRawOwnerAttachment_prefix_source
    (r : Request J S.cut)
    (A : (J).RawOwnerAttachment (reservedStrongSelectedStartingRecord r).record
      (strongSelectedPath U S K r)) : A.sourcePrefix.start ∈ Gamma.source :=
  A.prefix_starts_in_source (reservedStrongSelectedStartingRecord_grounded r)

/-- No relevant stopping-boundary point is lost inside the retained
starting-record prefix or the discarded part of that record. -/
theorem reservedStrongSelectedRawOwnerAttachment_prefix_disjoint_relevantBB
    (r : Request J S.cut)
    (A : (J).RawOwnerAttachment (reservedStrongSelectedStartingRecord r).record
      (strongSelectedPath U S K r)) :
    Disjoint (reservedStrongSelectedRelevantBB (L := L) (hL := hL) (S := S))
      A.sourcePrefix.support :=
  (reservedStrongSelectedStartingRecord_disjoint_relevantBB r).mono_right A.sourcePrefix_support

#print axioms exists_reservedStrongSelectedRawOwnerAttachment
#print axioms reservedStrongSelectedRawOwnerAttachment_prefix_source
#print axioms reservedStrongSelectedRawOwnerAttachment_prefix_disjoint_relevantBB

end DWeb.KappaLadder.Deferred
end Erdos599
