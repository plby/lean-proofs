/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.DeferredGroundingReservedSelection

/-!
# One relevant boundary for selected and reserved deferred records

The discarded family is indexed by `Option Request`: `none` is the actual
unused reserved record and `some r` is the final selected starting record for
request `r`.  Thus one input-level relevant boundary simultaneously avoids
the reserved record and every actual selected starting record.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace DWeb
namespace KappaLadder
namespace Deferred

open PopularGroundingBridge GroundingSimultaneousDecode

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}
variable {L : Gamma.KappaLadder kappa} {hL : IsKappaHindrance L}
variable {S : Popular.PopularSeparator (popularAuxiliaryIndexed L hL)}

local notation "J" => popularAuxiliaryInput L hL.legal

/-! ## Ordinary final selected family plus reservation -/

def reservedSelectedPruningSource :
    Option (Request J S.cut) → (J).lambda.source
  | none => (canonicalReservedRecord L hL S).auxiliarySource
  | some r => reservedSelectedSource r

def reservedSelectedPruningRecord :
    ∀ q : Option (Request J S.cut),
      DeferredAuxiliarySourceRecord L hL.legal
        (reservedSelectedPruningSource
          (L := L) (hL := hL) (S := S) q)
  | none => (canonicalReservedRecord L hL S).toAuxiliarySourceRecord
  | some r => reservedSelectedStartingRecord r

theorem reservedSelectedPruningCarrier_disjoint_cut
    (q : Option (Request J S.cut)) :
    Disjoint
      (PopularSwitching.ladderTrace J
          (reservedSelectedPruningRecord q).record ∪
        {(reservedSelectedPruningSource q).1}) S.cut := by
  cases q with
  | none =>
      exact (canonicalReservedRecord L hL S).ownCarrier_disjoint_cut
  | some r =>
      exact reservedSelectedStartingRecord_ownCarrier_disjoint_cut r

/-- The single ordinary-selector pruning datum discards both the final
selected starting records and the actual reserved record. -/
def reservedSelectedPruningData :
    GroundingInputRelevantPruning.Data J S.cut :=
  sourceRecordPruningData reservedSelectedPruningSource
    reservedSelectedPruningRecord reservedSelectedPruningCarrier_disjoint_cut

def reservedSelectedRelevantBB : Set V :=
  (reservedSelectedPruningData (L := L) (hL := hL) (S := S)).relevantBB

theorem canonicalReservedRecord_disjoint_reservedSelectedRelevantBB :
    Disjoint
      (reservedSelectedRelevantBB (L := L) (hL := hL) (S := S))
      (canonicalReservedRecord L hL S).record.support := by
  simpa only [reservedSelectedRelevantBB, reservedSelectedPruningData,
    reservedSelectedPruningRecord,
    DeferredCutAvoidingRecord.toAuxiliarySourceRecord] using
    sourceRecord_disjoint_relevantBB reservedSelectedPruningSource
      reservedSelectedPruningRecord
      reservedSelectedPruningCarrier_disjoint_cut
      (none : Option (Request J S.cut))

theorem reservedSelectedStartingRecord_disjoint_relevantBB
    (r : Request J S.cut) :
    Disjoint
      (reservedSelectedRelevantBB (L := L) (hL := hL) (S := S))
      (reservedSelectedStartingRecord r).record.support := by
  simpa only [reservedSelectedRelevantBB, reservedSelectedPruningData,
    reservedSelectedPruningRecord] using
    sourceRecord_disjoint_relevantBB reservedSelectedPruningSource
      reservedSelectedPruningRecord
      reservedSelectedPruningCarrier_disjoint_cut
      (some r)

theorem reservedSelectedRelevantFiniteDescentDecoder :
    GroundingInputRelevantDecoder.RelevantFiniteDescentDecoder
      (reservedSelectedPruningData (L := L) (hL := hL) (S := S)) :=
  GroundingInputRelevantDecoder.relevantFiniteDescentDecoder
    (reservedSelectedPruningData (L := L) (hL := hL) (S := S))
    (popularAuxiliary_sourceCovered L hL.legal)
    (popularAuxiliary_terminalCut_isSeparator L hL.legal)
    S.separates

theorem reservedSelectedRelevantBB_isSeparator :
    Popular.IsSeparator Gamma
      (reservedSelectedRelevantBB (L := L) (hL := hL) (S := S)) :=
  GroundingInputRelevantDecoder.relevantBB_isSeparator
    (reservedSelectedPruningData (L := L) (hL := hL) (S := S))
    (popularAuxiliary_sourceCovered L hL.legal)
    (popularAuxiliary_terminalCut_isSeparator L hL.legal)
    S.separates

/-! ## Strong final selected family plus the same reservation -/

def reservedStrongSelectedPruningSource :
    Option (Request J S.cut) → (J).lambda.source
  | none => (canonicalReservedRecord L hL S).auxiliarySource
  | some r => reservedStrongSelectedSource r

def reservedStrongSelectedPruningRecord :
    ∀ q : Option (Request J S.cut),
      DeferredAuxiliarySourceRecord L hL.legal
        (reservedStrongSelectedPruningSource
          (L := L) (hL := hL) (S := S) q)
  | none => (canonicalReservedRecord L hL S).toAuxiliarySourceRecord
  | some r => reservedStrongSelectedStartingRecord r

theorem reservedStrongSelectedPruningCarrier_disjoint_cut
    (q : Option (Request J S.cut)) :
    Disjoint
      (PopularSwitching.ladderTrace J
          (reservedStrongSelectedPruningRecord q).record ∪
        {(reservedStrongSelectedPruningSource q).1}) S.cut := by
  cases q with
  | none =>
      exact (canonicalReservedRecord L hL S).ownCarrier_disjoint_cut
  | some r =>
      exact reservedStrongSelectedStartingRecord_ownCarrier_disjoint_cut r

/-- The strong-selector pruning datum uses the same actual reserved record
and all actual strong-selected starting records. -/
def reservedStrongSelectedPruningData :
    GroundingInputRelevantPruning.Data J S.cut :=
  sourceRecordPruningData reservedStrongSelectedPruningSource
    reservedStrongSelectedPruningRecord
    reservedStrongSelectedPruningCarrier_disjoint_cut

def reservedStrongSelectedRelevantBB : Set V :=
  (reservedStrongSelectedPruningData
    (L := L) (hL := hL) (S := S)).relevantBB

theorem canonicalReservedRecord_disjoint_reservedStrongSelectedRelevantBB :
    Disjoint
      (reservedStrongSelectedRelevantBB (L := L) (hL := hL) (S := S))
      (canonicalReservedRecord L hL S).record.support := by
  simpa only [reservedStrongSelectedRelevantBB,
    reservedStrongSelectedPruningData, reservedStrongSelectedPruningRecord,
    DeferredCutAvoidingRecord.toAuxiliarySourceRecord] using
    sourceRecord_disjoint_relevantBB reservedStrongSelectedPruningSource
      reservedStrongSelectedPruningRecord
      reservedStrongSelectedPruningCarrier_disjoint_cut
      (none : Option (Request J S.cut))

theorem reservedStrongSelectedStartingRecord_disjoint_relevantBB
    (r : Request J S.cut) :
    Disjoint
      (reservedStrongSelectedRelevantBB (L := L) (hL := hL) (S := S))
      (reservedStrongSelectedStartingRecord r).record.support := by
  simpa only [reservedStrongSelectedRelevantBB,
    reservedStrongSelectedPruningData,
    reservedStrongSelectedPruningRecord] using
    sourceRecord_disjoint_relevantBB reservedStrongSelectedPruningSource
      reservedStrongSelectedPruningRecord
      reservedStrongSelectedPruningCarrier_disjoint_cut
      (some r)

theorem reservedStrongSelectedRelevantFiniteDescentDecoder :
    GroundingInputRelevantDecoder.RelevantFiniteDescentDecoder
      (reservedStrongSelectedPruningData
        (L := L) (hL := hL) (S := S)) :=
  GroundingInputRelevantDecoder.relevantFiniteDescentDecoder
    (reservedStrongSelectedPruningData (L := L) (hL := hL) (S := S))
    (popularAuxiliary_sourceCovered L hL.legal)
    (popularAuxiliary_terminalCut_isSeparator L hL.legal)
    S.separates

theorem reservedStrongSelectedRelevantBB_isSeparator :
    Popular.IsSeparator Gamma
      (reservedStrongSelectedRelevantBB
        (L := L) (hL := hL) (S := S)) :=
  GroundingInputRelevantDecoder.relevantBB_isSeparator
    (reservedStrongSelectedPruningData (L := L) (hL := hL) (S := S))
    (popularAuxiliary_sourceCovered L hL.legal)
    (popularAuxiliary_terminalCut_isSeparator L hL.legal)
    S.separates

end Deferred
end KappaLadder
end DWeb
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.Deferred.canonicalReservedRecord_disjoint_reservedSelectedRelevantBB
#print axioms
  Erdos599.DWeb.KappaLadder.Deferred.reservedStrongSelectedStartingRecord_disjoint_relevantBB
#print axioms
  Erdos599.DWeb.KappaLadder.Deferred.reservedStrongSelectedRelevantBB_isSeparator
