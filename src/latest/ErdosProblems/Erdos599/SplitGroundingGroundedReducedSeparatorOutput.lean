/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SplitGroundingGroundedReducedSeparator818
import ErdosProblems.Erdos599.SplitGroundingGroundedSeparatorOutput

/-!
# Assertion 8.22 output from the source-correct reduced boundary

The generic rooted-reachability compiler already accepts an arbitrary
separating frontier contained in the coarse boundary.  The reduced boundary
is such a frontier by the corrected Assertion 8.18 and by its literal subset
of the coarse boundary.  Thus the sole remaining construction-specific task
is rooting the reduced boundary in the relation stopped at that boundary.
-/

noncomputable section

open Cardinal Set

namespace Erdos599

open GroundingErasedDecode

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

namespace DWeb.KappaLadder

variable {L : Gamma.KappaLadder kappa} {hL : L.IsSplitKappaHindrance}
  {hground : Stationary.IsStationaryBelow kappa L.phiGround}
  {S : Popular.PopularSeparator
    (L.splitGroundedPopularAuxiliaryIndexed hL hground)}
  {K : GroundingSelection.Controls S}

private abbrev ReducedOutputInput :=
  L.splitGroundedPopularAuxiliaryInput hL.legal

private abbrev ReducedOutputIndexed :=
  L.splitGroundedPopularAuxiliaryIndexed hL hground

/-- Rooting the corrected reduced boundary in the relation stopped there
produces the exact Assertion 8.22 output. -/
theorem splitGroundedReducedAssertion822Output_of_rooted
    (R : L.SplitGroundedUnusedRecord hL hground S K)
    (hroot : ∀ t ∈ L.splitGroundedBB hL.legal S.cut,
      ∃ a ∈ Gamma.source \ {R.record.initial},
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ erasedSelectedSwitchedEdgesAt
            (ReducedOutputIndexed (L := L) (hL := hL)
              (hground := hground)) S K
                (L.splitGroundedBB hL.legal S.cut)) a t) :
    Nonempty (GroundingFinalAssembly.Assertion822Output
      (ReducedOutputInput (L := L) (hL := hL)) S.cut) := by
  apply L.splitGroundedAssertion822Output_of_frontierGeometry_withControls
    R (L.splitGroundedBB hL.legal S.cut)
  · exact L.splitGroundedBB_subset_legacyBB hL.legal S.cut
  · exact L.splitGroundedReducedAssertion8_18
      hL.legal S.cut S.separates
  · exact hroot

/-- The same corrected rooted-boundary geometry yields the required ambient
hindrance directly. -/
theorem exists_hindrance_of_splitGroundedReducedBB_rooted
    (R : L.SplitGroundedUnusedRecord hL hground S K)
    (hroot : ∀ t ∈ L.splitGroundedBB hL.legal S.cut,
      ∃ a ∈ Gamma.source \ {R.record.initial},
        Relation.ReflTransGen
          (fun x y ↦ (x, y) ∈ erasedSelectedSwitchedEdgesAt
            (ReducedOutputIndexed (L := L) (hL := hL)
              (hground := hground)) S K
                (L.splitGroundedBB hL.legal S.cut)) a t) :
    ∃ W : Set Gamma.DPath, Gamma.IsHindrance W :=
  exists_hindrance_of_splitGroundedAssertion822Output
    (L.splitGroundedReducedAssertion822Output_of_rooted R hroot).some

end DWeb.KappaLadder
end Erdos599

#print axioms Erdos599.DWeb.KappaLadder.splitGroundedReducedAssertion822Output_of_rooted
#print axioms Erdos599.DWeb.KappaLadder.exists_hindrance_of_splitGroundedReducedBB_rooted
