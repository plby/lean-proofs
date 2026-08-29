/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.DeferredGroundingCutAvoidingSelection
import ErdosProblems.Erdos599.GroundingSourceCarrierControls
import ErdosProblems.Erdos599.GroundingSourceIndexControls

/-!
# Grounded, cut-avoiding starting records for deferred selection

The deferred auxiliary contains sources for both grounded and hanging
records.  The latter have globally nonstationary indices.  Starting with the
existing deferred collision controls, we first exclude cut-contacting source
carriers and then exclude `phiHanging`.  Consequently every ordinary or
strong selected request starts on a grounded deferred record whose entire
encoded carrier avoids the popular cut.

This only controls the selected starting record.  It does not classify an
arbitrary equal-origin hanging component encountered later by the route.
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

/-- The deferred controls with both whole-source-carrier cut avoidance and
hanging-source-index exclusion.  Both refinements are additive to the
existing strict-prior and hanging-fragment controls. -/
noncomputable def groundedCarrierControls
    (L : Gamma.KappaLadder kappa) (hL : IsKappaHindrance L)
    (S : Popular.PopularSeparator (popularAuxiliaryIndexed L hL)) :
    GroundingSelection.Controls S :=
  let K := (selectionControls L hL S).withSourceCarrierCutAvoidance
    (deferredSourceCarrierFamily L hL.legal)
  K.withSourceIndexAvoidance (phiHanging L)
    (phiHanging_not_stationary L hL.legal)

namespace DeferredAuxiliarySourceRecord

/-- A deferred source record whose source index is not hanging is grounded.
The proof uses its literal chosen-stage provenance. -/
theorem grounded_of_sourceIndex_not_mem_phiHanging
    {x : (J).lambda.source}
    (R : DeferredAuxiliarySourceRecord L hL.legal x)
    (hnot : (U).f x ∉ phiHanging L) :
    R.record.initial ∈ Gamma.source := by
  have hindex : (U).f x = R.stage := by
    rw [show (U).f = auxiliarySourceIndex L hL.legal from
      (auxiliarySourceIndex_eq_sourceIndex L hL.legal).symm]
    exact R.source_index
  have hstageNot : R.stage ∉ phiHanging L := by
    simpa only [hindex] using hnot
  have hstageGround : R.stage ∈ phiGround L := by
    by_contra hnotGround
    exact hstageNot ⟨R.stage_mem_phi, hnotGround⟩
  obtain ⟨p, hpChosen, hpGround⟩ := hstageGround
  have hpEq : p = R.record :=
    Option.some.inj (hpChosen.symm.trans R.chosen)
  exact hpEq ▸ hpGround

end DeferredAuxiliarySourceRecord

/-- The actual auxiliary source of the ordinary selected request. -/
def selectedSource (r : Request J S.cut) : (J).lambda.source :=
  ⟨(GroundingAssembly.selectedPath U S
      (groundedCarrierControls L hL S) r).start,
    (GroundingAssembly.selectedWarp U S
      (groundedCarrierControls L hL S)).starts_in_source ⟨r, rfl⟩⟩

/-- The literal deferred record represented by the ordinary selected source. -/
def selectedStartingRecord (r : Request J S.cut) :
    DeferredAuxiliarySourceRecord L hL.legal (selectedSource r) :=
  deferredAuxiliarySourceRecord L hL.legal (selectedSource r)

/-- The ordinary selected source index is not hanging. -/
theorem selectedSource_index_not_mem_phiHanging
    (r : Request J S.cut) :
    (U).f (selectedSource r) ∉ phiHanging L := by
  simpa only [selectedSource, groundedCarrierControls] using
    GroundingSelection.selectedPath_sourceIndex_not_mem S
      ((selectionControls L hL S).withSourceCarrierCutAvoidance
        (deferredSourceCarrierFamily L hL.legal))
      (phiHanging L) (phiHanging_not_stationary L hL.legal) r

/-- Every ordinary selected request starts on a grounded record. -/
theorem selectedStartingRecord_grounded (r : Request J S.cut) :
    (selectedStartingRecord r).record.initial ∈ Gamma.source :=
  (selectedStartingRecord r).grounded_of_sourceIndex_not_mem_phiHanging
    (selectedSource_index_not_mem_phiHanging r)

/-- The whole source carrier of the ordinary selected request avoids the
popular cut. -/
theorem selectedSource_carrier_disjoint_cut (r : Request J S.cut) :
    Disjoint ((deferredSourceCarrierFamily L hL.legal).carrier
      (selectedSource r)) S.cut := by
  apply GroundingSelection.sourceCarrier_disjoint_cut_of_not_mem_cutContactPaths
  intro hbad
  apply GroundingAssembly.selectedPath_not_mem_hangingFragment
    U S (groundedCarrierControls L hL S) r
  exact Or.inl (Or.inr hbad)

/-- The selected record's literal trace, including its source proxy, avoids
the popular cut. -/
theorem selectedStartingRecord_ownCarrier_disjoint_cut
    (r : Request J S.cut) :
    Disjoint (PopularSwitching.ladderTrace J
        (selectedStartingRecord r).record ∪ {(selectedSource r).1})
      S.cut := by
  simpa only [deferredSourceCarrierFamily, selectedStartingRecord,
    deferredAuxiliarySourceRecord] using selectedSource_carrier_disjoint_cut r

/-- The actual auxiliary source of the strong selected request. -/
def strongSelectedSource (r : Request J S.cut) : (J).lambda.source :=
  ⟨(strongSelectedPath U S (groundedCarrierControls L hL S) r).start,
    (strongSelectedWarp U S
      (groundedCarrierControls L hL S)).starts_in_source ⟨r, rfl⟩⟩

/-- The literal deferred record represented by the strong selected source. -/
def strongSelectedStartingRecord (r : Request J S.cut) :
    DeferredAuxiliarySourceRecord L hL.legal (strongSelectedSource r) :=
  deferredAuxiliarySourceRecord L hL.legal (strongSelectedSource r)

/-- The strong selected source index is not hanging. -/
theorem strongSelectedSource_index_not_mem_phiHanging
    (r : Request J S.cut) :
    (U).f (strongSelectedSource r) ∉ phiHanging L := by
  simpa only [strongSelectedSource, groundedCarrierControls] using
    GroundingSelection.strongSelectedPath_sourceIndex_not_mem S
      ((selectionControls L hL S).withSourceCarrierCutAvoidance
        (deferredSourceCarrierFamily L hL.legal))
      (phiHanging L) (phiHanging_not_stationary L hL.legal) r

/-- Every strong selected request starts on a grounded record. -/
theorem strongSelectedStartingRecord_grounded (r : Request J S.cut) :
    (strongSelectedStartingRecord r).record.initial ∈ Gamma.source :=
  (strongSelectedStartingRecord r).grounded_of_sourceIndex_not_mem_phiHanging
    (strongSelectedSource_index_not_mem_phiHanging r)

/-- The whole source carrier of the strong selected request avoids the
popular cut. -/
theorem strongSelectedSource_carrier_disjoint_cut (r : Request J S.cut) :
    Disjoint ((deferredSourceCarrierFamily L hL.legal).carrier
      (strongSelectedSource r)) S.cut := by
  apply GroundingSelection.sourceCarrier_disjoint_cut_of_not_mem_cutContactPaths
  intro hbad
  apply strongSelectedPath_not_mem_hangingFragment
    U S (groundedCarrierControls L hL S) r
  exact Or.inl (Or.inr hbad)

/-- The strong selected record's literal trace and source proxy avoid the
popular cut. -/
theorem strongSelectedStartingRecord_ownCarrier_disjoint_cut
    (r : Request J S.cut) :
    Disjoint (PopularSwitching.ladderTrace J
        (strongSelectedStartingRecord r).record ∪
      {(strongSelectedSource r).1}) S.cut := by
  simpa only [deferredSourceCarrierFamily, strongSelectedStartingRecord,
    deferredAuxiliarySourceRecord] using
      strongSelectedSource_carrier_disjoint_cut r

end Deferred
end KappaLadder
end DWeb
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.Deferred.groundedCarrierControls
#print axioms
  Erdos599.DWeb.KappaLadder.Deferred.selectedStartingRecord_grounded
#print axioms
  Erdos599.DWeb.KappaLadder.Deferred.strongSelectedStartingRecord_ownCarrier_disjoint_cut
