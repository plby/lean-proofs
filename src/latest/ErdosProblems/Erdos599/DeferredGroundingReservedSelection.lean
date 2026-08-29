/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.DeferredGroundingStartingRelevantPruning

/-!
# Reserving an actual unused deferred grounded record

Choose the cut-avoiding unused record against the grounded-carrier controls,
then refine those controls by excluding every later selected route which
meets the reserved carrier away from its own request apex.  The resulting
ordinary and strong selectors retain the grounded-source and source-carrier
avoidance properties.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace DWeb
namespace KappaLadder
namespace Deferred

open _root_.Erdos599.DirectedPath Stationary PopularGroundingBridge
open GroundingSimultaneousDecode

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}
variable {L : Gamma.KappaLadder kappa} {hL : IsKappaHindrance L}
variable {S : Popular.PopularSeparator (popularAuxiliaryIndexed L hL)}

local notation "J" => popularAuxiliaryInput L hL.legal
local notation "U" => popularAuxiliaryIndexed L hL

/-- The actual unused, grounded, cut-avoiding record selected against the
grounded-carrier control package. -/
noncomputable def canonicalReservedRecord
    (L : Gamma.KappaLadder kappa) (hL : IsKappaHindrance L)
    (S : Popular.PopularSeparator (popularAuxiliaryIndexed L hL)) :
    DeferredCutAvoidingRecord L hL S (groundedCarrierControls L hL S) :=
  Classical.choice
    (exists_deferredCutAvoidingRecord L hL S
      (groundedCarrierControls L hL S))

/-- Full trace plus source proxy of the reserved deferred record. -/
def deferredReservedRecordCarrier
    {K : GroundingSelection.Controls S}
    (R : DeferredCutAvoidingRecord L hL S K) : Set (J).LV :=
  PopularSwitching.ladderTrace J R.record ∪ {R.auxiliarySource.1}

theorem deferredReservedRecordCarrier_countable
    {K : GroundingSelection.Controls S}
    (R : DeferredCutAvoidingRecord L hL S K) :
    (deferredReservedRecordCarrier R).Countable :=
  (PopularSwitching.ladderTrace_countable J R.record).union
    (Set.countable_singleton R.auxiliarySource.1)

/-- Local paths contacting the reserved carrier away from their own apex. -/
def deferredReservedRecordCollidingPaths
    {K : GroundingSelection.Controls S}
    (R : DeferredCutAvoidingRecord L hL S K)
    (r : Request J S.cut) : Set (FinitePath (J).lambda.graph) :=
  {p | ∃ x ∈ deferredReservedRecordCarrier R \ {requestAuxVertex r},
    x ∈ p.support}

theorem deferredReservedRecordCollidingIndices_nonstationary
    {K : GroundingSelection.Controls S}
    (R : DeferredCutAvoidingRecord L hL S K) (r : Request J S.cut) :
    ¬ IsStationaryBelow kappa
      (GroundingSelection.restrictedIndices U (requestFan S r)
        (deferredReservedRecordCollidingPaths R r)) := by
  apply
    PopularAuxiliary.Input.joinedFamily_initialIndices_nonstationary_of_meets_countable
      U
      (PopularSwitching.restrictPaths (requestFan S r)
        (deferredReservedRecordCollidingPaths R r))
      ((deferredReservedRecordCarrier_countable R).mono Set.sdiff_subset)
      Set.disjoint_sdiff_left
  intro p hp
  obtain ⟨x, hxCarrier, hxp⟩ := hp.2
  exact ⟨x, hxCarrier, hxp⟩

/-- Add reserved-record avoidance to an arbitrary existing deferred control
package. -/
noncomputable def reservedControlsFrom
    (K : GroundingSelection.Controls S)
    (R : DeferredCutAvoidingRecord L hL S K) :
    GroundingSelection.Controls S := {
  hangingLadder := K.hangingLadder
  hangingFragment := fun r ↦
    K.hangingFragment r ∪ deferredReservedRecordCollidingPaths R r
  ladderRank := K.ladderRank
  ladderTrace := K.ladderTrace
  ladderRank_regressive := K.ladderRank_regressive
  ladderTrace_countable := K.ladderTrace_countable
  ladderTrace_disjoint_apex := K.ladderTrace_disjoint_apex
  hangingLadder_meets := K.hangingLadder_meets
  fragmentIndices_nonstationary := by
    intro r hstationary
    apply GroundingSelection.not_isStationaryBelow_union
      hL.legal.regular hL.legal.uncountable
      (K.fragmentIndices_nonstationary r)
      (deferredReservedRecordCollidingIndices_nonstationary R r)
    exact hstationary.mono
      (GroundingControlledAssembly.restrictedIndices_union_subset
        U (requestFan S r) (K.hangingFragment r)
          (deferredReservedRecordCollidingPaths R r)) }

/-- Canonical controls carrying all previous deferred exclusions and the
actual reserved-record exclusion. -/
noncomputable def reservedGroundedCarrierControls
    (L : Gamma.KappaLadder kappa) (hL : IsKappaHindrance L)
    (S : Popular.PopularSeparator (popularAuxiliaryIndexed L hL)) :
    GroundingSelection.Controls S :=
  reservedControlsFrom (groundedCarrierControls L hL S)
    (canonicalReservedRecord L hL S)

namespace DeferredCutAvoidingRecord

/-- View the reserved record as the literal source record represented by its
stored auxiliary source. -/
def toAuxiliarySourceRecord
    {K : GroundingSelection.Controls S}
    (R : DeferredCutAvoidingRecord L hL S K) :
    DeferredAuxiliarySourceRecord L hL.legal R.auxiliarySource where
  stage := R.stage
  record := R.record
  stage_mem_phi :=
    ((bookkeeping L).mem_phi_iff_exists_chosen
      hL.legal.validBookkeeping).2 ⟨R.record, R.chosen⟩
  chosen := R.chosen
  limit_inessential := R.limit_inessential
  represents := R.source_represents
  source_index := by
    rw [auxiliarySourceIndex_eq_sourceIndex L hL.legal]
    exact R.source_index

theorem ownCarrier_disjoint_cut
    {K : GroundingSelection.Controls S}
    (R : DeferredCutAvoidingRecord L hL S K) :
    Disjoint (deferredReservedRecordCarrier R) S.cut := by
  apply Set.disjoint_left.mpr
  intro x hx hxCut
  rcases hx with hxTrace | hxSource
  · exact Set.disjoint_left.mp R.trace_disjoint hxTrace hxCut
  · exact R.auxiliarySource_not_mem_cut (hxSource ▸ hxCut)

end DeferredCutAvoidingRecord

/-! ## Final ordinary selector -/

def reservedSelectedSource (r : Request J S.cut) : (J).lambda.source :=
  ⟨(GroundingAssembly.selectedPath U S
      (reservedGroundedCarrierControls L hL S) r).start,
    (GroundingAssembly.selectedWarp U S
      (reservedGroundedCarrierControls L hL S)).starts_in_source ⟨r, rfl⟩⟩

def reservedSelectedStartingRecord (r : Request J S.cut) :
    DeferredAuxiliarySourceRecord L hL.legal (reservedSelectedSource r) :=
  deferredAuxiliarySourceRecord L hL.legal (reservedSelectedSource r)

theorem reservedSelectedSource_index_not_mem_phiHanging
    (r : Request J S.cut) :
    (U).f (reservedSelectedSource r) ∉ phiHanging L := by
  intro hindex
  apply GroundingAssembly.selectedPath_not_mem_hangingFragment
    U S (reservedGroundedCarrierControls L hL S) r
  exact Or.inl (Or.inr ⟨reservedSelectedSource r, rfl, hindex⟩)

theorem reservedSelectedStartingRecord_grounded (r : Request J S.cut) :
    (reservedSelectedStartingRecord r).record.initial ∈ Gamma.source :=
  (reservedSelectedStartingRecord r).grounded_of_sourceIndex_not_mem_phiHanging
    (reservedSelectedSource_index_not_mem_phiHanging r)

theorem reservedSelectedSource_carrier_disjoint_cut
    (r : Request J S.cut) :
    Disjoint ((deferredSourceCarrierFamily L hL.legal).carrier
      (reservedSelectedSource r)) S.cut := by
  apply GroundingSelection.sourceCarrier_disjoint_cut_of_not_mem_cutContactPaths
  intro hbad
  apply GroundingAssembly.selectedPath_not_mem_hangingFragment
    U S (reservedGroundedCarrierControls L hL S) r
  exact Or.inl (Or.inl (Or.inr hbad))

theorem reservedSelectedStartingRecord_ownCarrier_disjoint_cut
    (r : Request J S.cut) :
    Disjoint (PopularSwitching.ladderTrace J
        (reservedSelectedStartingRecord r).record ∪
      {(reservedSelectedSource r).1}) S.cut := by
  simpa only [deferredSourceCarrierFamily, reservedSelectedStartingRecord,
    deferredAuxiliarySourceRecord] using
      reservedSelectedSource_carrier_disjoint_cut r

/-! ## Final strong selector -/

def reservedStrongSelectedSource (r : Request J S.cut) : (J).lambda.source :=
  ⟨(strongSelectedPath U S
      (reservedGroundedCarrierControls L hL S) r).start,
    (strongSelectedWarp U S
      (reservedGroundedCarrierControls L hL S)).starts_in_source ⟨r, rfl⟩⟩

def reservedStrongSelectedStartingRecord (r : Request J S.cut) :
    DeferredAuxiliarySourceRecord L hL.legal
      (reservedStrongSelectedSource r) :=
  deferredAuxiliarySourceRecord L hL.legal (reservedStrongSelectedSource r)

theorem reservedStrongSelectedSource_index_not_mem_phiHanging
    (r : Request J S.cut) :
    (U).f (reservedStrongSelectedSource r) ∉ phiHanging L := by
  intro hindex
  apply strongSelectedPath_not_mem_hangingFragment
    U S (reservedGroundedCarrierControls L hL S) r
  exact Or.inl (Or.inr ⟨reservedStrongSelectedSource r, rfl, hindex⟩)

theorem reservedStrongSelectedStartingRecord_grounded
    (r : Request J S.cut) :
    (reservedStrongSelectedStartingRecord r).record.initial ∈ Gamma.source :=
  (reservedStrongSelectedStartingRecord r).grounded_of_sourceIndex_not_mem_phiHanging
    (reservedStrongSelectedSource_index_not_mem_phiHanging r)

theorem reservedStrongSelectedSource_carrier_disjoint_cut
    (r : Request J S.cut) :
    Disjoint ((deferredSourceCarrierFamily L hL.legal).carrier
      (reservedStrongSelectedSource r)) S.cut := by
  apply GroundingSelection.sourceCarrier_disjoint_cut_of_not_mem_cutContactPaths
  intro hbad
  apply strongSelectedPath_not_mem_hangingFragment
    U S (reservedGroundedCarrierControls L hL S) r
  exact Or.inl (Or.inl (Or.inr hbad))

theorem reservedStrongSelectedStartingRecord_ownCarrier_disjoint_cut
    (r : Request J S.cut) :
    Disjoint (PopularSwitching.ladderTrace J
        (reservedStrongSelectedStartingRecord r).record ∪
      {(reservedStrongSelectedSource r).1}) S.cut := by
  simpa only [deferredSourceCarrierFamily,
    reservedStrongSelectedStartingRecord, deferredAuxiliarySourceRecord] using
      reservedStrongSelectedSource_carrier_disjoint_cut r

/-! ## Reserved contact exclusion and the actual unused-source defect -/

theorem reservedSelectedPath_no_offApex_reserved_contact
    (r : Request J S.cut) {x : (J).LV}
    (hxCarrier : x ∈ deferredReservedRecordCarrier
      (canonicalReservedRecord L hL S))
    (hxApex : x ≠ requestAuxVertex r) :
    x ∉ (GroundingAssembly.selectedPath U S
      (reservedGroundedCarrierControls L hL S) r).support := by
  intro hxPath
  apply GroundingAssembly.selectedPath_not_mem_hangingFragment
    U S (reservedGroundedCarrierControls L hL S) r
  exact Or.inr ⟨x, ⟨hxCarrier, by
    simpa only [Set.mem_singleton_iff]⟩, hxPath⟩

theorem reservedStrongSelectedPath_no_offApex_reserved_contact
    (r : Request J S.cut) {x : (J).LV}
    (hxCarrier : x ∈ deferredReservedRecordCarrier
      (canonicalReservedRecord L hL S))
    (hxApex : x ≠ requestAuxVertex r) :
    x ∉ (strongSelectedPath U S
      (reservedGroundedCarrierControls L hL S) r).support := by
  intro hxPath
  apply strongSelectedPath_not_mem_hangingFragment
    U S (reservedGroundedCarrierControls L hL S) r
  exact Or.inr ⟨x, ⟨hxCarrier, by
    simpa only [Set.mem_singleton_iff]⟩, hxPath⟩

theorem reservedSelectedPath_start_ne_reservedSource
    (r : Request J S.cut) :
    (GroundingAssembly.selectedPath U S
      (reservedGroundedCarrierControls L hL S) r).start ≠
      (canonicalReservedRecord L hL S).auxiliarySource.1 := by
  intro hstart
  let R := canonicalReservedRecord L hL S
  apply reservedSelectedPath_no_offApex_reserved_contact r
    (x := R.auxiliarySource.1) (Or.inr rfl)
  · intro heq
    exact R.auxiliarySource_not_mem_cut
      (heq ▸ requestAuxVertex_mem_cut r)
  · rw [← hstart]
    exact (GroundingAssembly.selectedPath U S
      (reservedGroundedCarrierControls L hL S) r).start_mem_support

theorem reservedStrongSelectedPath_start_ne_reservedSource
    (r : Request J S.cut) :
    (strongSelectedPath U S
      (reservedGroundedCarrierControls L hL S) r).start ≠
      (canonicalReservedRecord L hL S).auxiliarySource.1 := by
  intro hstart
  let R := canonicalReservedRecord L hL S
  apply reservedStrongSelectedPath_no_offApex_reserved_contact r
    (x := R.auxiliarySource.1) (Or.inr rfl)
  · intro heq
    exact R.auxiliarySource_not_mem_cut
      (heq ▸ requestAuxVertex_mem_cut r)
  · rw [← hstart]
    exact (strongSelectedPath U S
      (reservedGroundedCarrierControls L hL S) r).start_mem_support

/-- The reserved record remains genuinely unused by the final ordinary
selected family, even though it was originally chosen against the preceding
grounded-carrier controls. -/
theorem canonicalReservedRecord_stage_unused_selected :
    (canonicalReservedRecord L hL S).stage ∉
      Popular.initialIndicesOf U
        (GroundingAssembly.selectedWarp U S
          (reservedGroundedCarrierControls L hL S)).paths
        (GroundingAssembly.selectedWarp U S
          (reservedGroundedCarrierControls L hL S)).starts_in_source := by
  rintro ⟨p, hp, hindex⟩
  obtain ⟨r, rfl⟩ := hp
  let R := canonicalReservedRecord L hL S
  have hsource : reservedSelectedSource r = R.auxiliarySource :=
    popularAuxiliaryIndexed_sourceIndexed L hL
      (hindex.trans R.source_index.symm)
  exact reservedSelectedPath_start_ne_reservedSource r
    (congrArg Subtype.val hsource)

/-- The same actual unused-source defect holds for the final strong selected
family. -/
theorem canonicalReservedRecord_stage_unused_strongSelected :
    (canonicalReservedRecord L hL S).stage ∉
      Popular.initialIndicesOf U
        (strongSelectedWarp U S
          (reservedGroundedCarrierControls L hL S)).paths
        (strongSelectedWarp U S
          (reservedGroundedCarrierControls L hL S)).starts_in_source := by
  rintro ⟨p, hp, hindex⟩
  obtain ⟨r, rfl⟩ := hp
  let R := canonicalReservedRecord L hL S
  have hsource : reservedStrongSelectedSource r = R.auxiliarySource :=
    popularAuxiliaryIndexed_sourceIndexed L hL
      (hindex.trans R.source_index.symm)
  exact reservedStrongSelectedPath_start_ne_reservedSource r
    (congrArg Subtype.val hsource)

end Deferred
end KappaLadder
end DWeb
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.Deferred.reservedGroundedCarrierControls
#print axioms
  Erdos599.DWeb.KappaLadder.Deferred.reservedStrongSelectedStartingRecord_grounded
#print axioms
  Erdos599.DWeb.KappaLadder.Deferred.reservedStrongSelectedPath_start_ne_reservedSource
#print axioms
  Erdos599.DWeb.KappaLadder.Deferred.canonicalReservedRecord_stage_unused_selected
