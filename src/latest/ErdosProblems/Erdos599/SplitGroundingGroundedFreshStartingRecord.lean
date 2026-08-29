/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SplitGroundingGroundedFreshAvoidingCanonical
import ErdosProblems.Erdos599.SplitGroundingGroundedSourceRecordCutAvoiding

/-!
# Every canonical selected starting component avoids the relevant boundary

The canonical control package now excludes the globally nonstationary source
indices whose whole record carriers meet the popular cut.  This is stronger
than reserving one unused record: every selected request has a starting
record disjoint from the relevant boundary.  It supplies the starting-owner
avoidance required when replacing its old tail by a selected route suffix.

The nonstationary-fresh hypothesis of this existing control branch remains
explicit; this module does not eliminate arbitrary equal-origin hanging
collisions or claim the final switch/prune theorem.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599.DWeb.KappaLadder

open GroundingSimultaneousDecode PopularGroundingBridge

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}
variable {L : Gamma.KappaLadder kappa} {hL : L.IsSplitKappaHindrance}
variable {hground : Stationary.IsStationaryBelow kappa L.phiGround}
variable {hnotFresh : ¬ Stationary.IsStationaryBelow kappa
  L.freshInessentialGroundStages}
variable {S : Popular.PopularSeparator
  (L.splitGroundedPopularAuxiliaryIndexed hL hground)}

local notation "J" => L.splitGroundedPopularAuxiliaryInput hL.legal
local notation "U" => L.splitGroundedPopularAuxiliaryIndexed hL hground
local notation "K" => L.splitGroundedFreshAvoidingCanonicalControls hL hground hnotFresh S

/-- The actual auxiliary source of the canonical selected request. -/
def splitGroundedFreshAvoidingCanonicalSelectedSource
    (r : Request J S.cut) : (J).lambda.source :=
  ⟨(strongSelectedPath U S K r).start,
    (strongSelectedWarp U S K).starts_in_source ⟨r, rfl⟩⟩

/-- The literal recorded component represented by that source, retaining
its chosen stage and representation rather than selecting another owner. -/
def splitGroundedFreshAvoidingCanonicalStartingRecord
    (r : Request J S.cut) :
    L.SplitGroundedAuxiliarySourceRecord hL.legal
      (splitGroundedFreshAvoidingCanonicalSelectedSource
        (hnotFresh := hnotFresh) r) :=
  L.splitGroundedAuxiliarySourceRecord hL.legal
    (splitGroundedFreshAvoidingCanonicalSelectedSource
      (hnotFresh := hnotFresh) r)

/-- The added exceptional-source family survives both the fresh-collision
and reserved-record refinements of the controls. -/
theorem splitGroundedFreshAvoidingCanonicalSelectedSource_carrier_disjoint_cut
    (r : Request J S.cut) :
    Disjoint ((L.splitGroundedSourceCarrierFamily hL.legal).carrier
      (splitGroundedFreshAvoidingCanonicalSelectedSource
        (hnotFresh := hnotFresh) r)) S.cut := by
  apply GroundingSelection.sourceCarrier_disjoint_cut_of_not_mem_cutContactPaths
  intro hbad
  apply strongSelectedPath_not_mem_hangingFragment U S K r
  exact Or.inl (Or.inl (Or.inr hbad))

/-- Whole encoded starting-record avoidance, including its source proxy
when the record is a ray. -/
theorem splitGroundedFreshAvoidingCanonicalStartingRecord_ownCarrier_disjoint_cut
    (r : Request J S.cut) :
    Disjoint (PopularSwitching.ladderTrace J
        (splitGroundedFreshAvoidingCanonicalStartingRecord
          (hnotFresh := hnotFresh) r).record ∪
      {(splitGroundedFreshAvoidingCanonicalSelectedSource
        (hnotFresh := hnotFresh) r).1}) S.cut :=
  splitGroundedFreshAvoidingCanonicalSelectedSource_carrier_disjoint_cut r

/-- The old starting component can be discarded after its last selected
contact without losing a point of the relevant boundary on that component. -/
theorem splitGroundedFreshAvoidingCanonicalStartingRecord_disjoint_relevantBB
    (r : Request J S.cut) :
    Disjoint (L.splitGroundedRelevantBB hL.legal S.cut)
      (splitGroundedFreshAvoidingCanonicalStartingRecord
        (hnotFresh := hnotFresh) r).record.support := by
  exact
    (splitGroundedFreshAvoidingCanonicalStartingRecord
      (hnotFresh := hnotFresh) r).relevantBB_disjoint_record_of_ownCarrier_disjoint
        (splitGroundedFreshAvoidingCanonicalSelectedSource
          (hnotFresh := hnotFresh) r)
        (splitGroundedFreshAvoidingCanonicalStartingRecord_ownCarrier_disjoint_cut r)

#print axioms splitGroundedFreshAvoidingCanonicalSelectedSource_carrier_disjoint_cut
#print axioms splitGroundedFreshAvoidingCanonicalStartingRecord_disjoint_relevantBB

end Erdos599.DWeb.KappaLadder
