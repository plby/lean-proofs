/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SplitGroundingGroundedReachableRootDefect
import ErdosProblems.Erdos599.SplitGroundingGroundedReachableBoundaryNormal

/-!
# Fully concrete reachable defects of the canonical grounded split switch

This is the lossless public dispatcher after the generic simultaneous
realization, source-reachable boundary restriction, nonessential reserved
root compiler, ambient last-deleted-head extraction, and first-hit boundary
normalization.  Every unsuccessful root branch carries an actual finite
ambient prefix and an exact deleted-edge class; the ordered branch carries
its exact first-hit owners.
-/

noncomputable section

open Cardinal Set

namespace Erdos599

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

namespace DWeb.KappaLadder

/-- Fully concrete result of the canonical grounded split separator switch.
The remaining constructors are genuine exchange problems, not callbacks or
unstructured reachability premises. -/
theorem splitGroundedCanonicalAssertion822Output_or_concreteReachableDefect
    (L : Gamma.KappaLadder kappa) (hL : L.IsSplitKappaHindrance)
    (hground : Stationary.IsStationaryBelow kappa L.phiGround)
    (S : Popular.PopularSeparator
      (L.splitGroundedPopularAuxiliaryIndexed hL hground)) :
    Nonempty (GroundingFinalAssembly.Assertion822Output
        (L.splitGroundedPopularAuxiliaryInput hL.legal) S.cut) ∨
      (∃ O : L.SplitGroundedReachableEssentialReservedRootObstruction
          (hL := hL) (hground := hground) (S := S),
        L.SplitGroundedEssentialReservedAmbientDefectOutcome O) ∨
      (∃ O : L.SplitGroundedReachableWholeSourceRootObstruction
          (L.splitGroundedCanonicalUnusedRecord hL hground S),
        ∃ data : L.SplitGroundedWholeSourceAmbientLastDeletedHeadData O,
          L.SplitGroundedWholeSourceAmbientDeletedHeadOutcome O data) ∨
      (∃ O : L.SplitGroundedReachableBoundaryObstruction
          (L.splitGroundedCanonicalUnusedRecord hL hground S),
        SplitGroundedReachableFirstBoundarySinkOutcome O) := by
  rcases L.splitGroundedCanonicalAssertion822Output_or_reachableEssentialObstruction
      hL hground S with houtput | hessential | hwhole | hboundary
  · exact Or.inl houtput
  · right
    left
    let O := hessential.some
    exact ⟨O, O.ambientDefectOutcome⟩
  · right
    right
    left
    let O := hwhole.some
    let data := O.exists_ambientLastDeletedHeadData.some
    exact ⟨O, data, data.outcome⟩
  · right
    right
    right
    let O := hboundary.some
    exact ⟨O, O.firstBoundarySinkOutcome⟩

end DWeb.KappaLadder
end Erdos599

#print axioms
  Erdos599.DWeb.KappaLadder.splitGroundedCanonicalAssertion822Output_or_concreteReachableDefect
