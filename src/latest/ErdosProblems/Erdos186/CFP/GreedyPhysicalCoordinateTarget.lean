/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.GreedyPhysicalTarget
import ErdosProblems.Erdos186.CFP.RandomGreedyCorollary217Density

/-!
# Transporting physical greedy targets to one global coordinate system

The approximation ranks and stopping levels used to construct the colored
reserves may vary.  Once the physical subset-sum lower bound is known, this
module transports it through a single later centered identification map.
Thus no color approximation rank occurs in the statement.
-/

namespace Erdos186.CFP.RandomPartition

noncomputable section

set_option autoImplicit false

/-- A physical-target reserve remains at least as large after all of its
subset sums are mapped into any proper centered bounding-box coordinates
containing the source. -/
theorem PhysicalTargetRun.target_le_card_centeredCoordinateSubsetSums
    {W S : Finset ℤ} {d cap target : ℕ}
    (R : Greedy.PhysicalTargetRun S cap target)
    (hSW : S ⊆ W)
    (P : BoundingBox.BoundingGAP W d) (hproper : P.progression.Proper)
    (hzero : 0 ∈ W) :
    target ≤
      (GAP.subsetSums
        ((Greedy.selected S R.steps).image
          (Preprocessing.centeredIdentification P hproper hzero))).card := by
  exact R.target_le_subsetSums.trans
    (Preprocessing.card_integerSubsetSums_le_centeredCoordinateSubsetSums
      ((R.selected_subset).trans hSW) P hproper hzero)

/-- Unbundled canonical form of the same transport. -/
theorem target_le_card_centeredPhysicalTargetSubsetSums
    {W S : Finset ℤ} {d cap target : ℕ}
    (hcap : cap ≤ S.card)
    (hend : target ≤ (Greedy.sums S cap).card)
    (hSW : S ⊆ W)
    (P : BoundingBox.BoundingGAP W d) (hproper : P.progression.Proper)
    (hzero : 0 ∈ W) :
    target ≤
      (GAP.subsetSums
        ((Greedy.selected S (Greedy.physicalTargetStep S cap target)).image
          (Preprocessing.centeredIdentification P hproper hzero))).card := by
  exact PhysicalTargetRun.target_le_card_centeredCoordinateSubsetSums
    (Greedy.physicalTargetRun S cap target hcap hend)
      hSW P hproper hzero

end

end Erdos186.CFP.RandomPartition

#print axioms
  Erdos186.CFP.RandomPartition.PhysicalTargetRun.target_le_card_centeredCoordinateSubsetSums
